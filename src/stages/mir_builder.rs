use std::{
    collections::HashMap,
    ops::{Deref, DerefMut, Index, IndexMut},
};

use crate::ir2::{
    cst::UnaryOp,
    hir::{self, Thir, Type},
    mir::*,
};

pub fn lower(thir: &Thir) -> Mir {
    let mut builder = Builder::new();

    for function in &thir.functions {
        lower_function(thir, &mut builder, function);
    }

    builder.build()
}

fn lower_function(thir: &Thir, builder: &mut Builder, function: &hir::Function) {
    let mut builder = builder.function(function);

    let block = thir.get_block(function.entry);
    let result = lower_block(thir, &mut builder, block);

    // If the block resolves to a value of the same type as the return value, then it's an implicit
    // return.
    if thir.get_expr_ty(block.expr) == &function.return_ty {
        builder.store(LocalId::new(0), RValue::Use(result));
    }

    // Function block must always terminate with a return.
    if matches!(builder.current_block().terminator, Terminator::Unterminated) {
        builder.terminate(Terminator::Return);
    }
}

fn lower_block(thir: &Thir, builder: &mut FunctionBuilder<'_>, block: &hir::Block) -> Operand {
    for statement in &block.statements {
        match statement {
            hir::Statement::Declare(hir::DeclareStatement { binding, ty }) => {
                builder.add_binding(
                    *binding,
                    match ty {
                        hir::DeclarationTy::Type(ty) => ty,
                        hir::DeclarationTy::Inferred(expr) => thir.get_expr_ty(*expr),
                    }
                    .clone(),
                );
            }
            hir::Statement::Return(hir::ReturnStatement { expr }) => {
                let value = lower_expr(thir, builder, *expr);
                builder.store(LocalId::new(0), RValue::Use(value));
            }
            hir::Statement::Expr(hir::ExprStatement { expr }) => {
                lower_expr(thir, builder, *expr);
            }
        }
    }

    lower_expr(thir, builder, block.expr)
}

fn lower_expr(thir: &Thir, builder: &mut FunctionBuilder<'_>, expr: hir::ExprId) -> Operand {
    match thir.get_expr(expr) {
        hir::Expr::Assign(hir::Assign { variable, value }) => {
            let value = lower_expr(thir, builder, *value);
            let place = expr_to_place(thir, builder, *variable);
            builder.assign(place, RValue::Use(value));

            Operand::Constant(Constant::Unit)
        }
        hir::Expr::Binary(hir::Binary { lhs, op, rhs }) => {
            let lhs = lower_expr(thir, builder, *lhs);
            let rhs = lower_expr(thir, builder, *rhs);

            let result = builder.add_local(thir.get_expr_ty(expr).clone());

            builder.store(
                result,
                RValue::Binary(Binary {
                    lhs,
                    op: op.clone(),
                    rhs,
                }),
            );

            Operand::Place(Place {
                local: result,
                projection: vec![],
            })
        }
        hir::Expr::Unary(hir::Unary { op, value }) => {
            let value = lower_expr(thir, builder, *value);

            let result = builder.add_local(thir.get_expr_ty(expr).clone());

            builder.store(
                result,
                RValue::Unary(Unary {
                    value,
                    op: op.clone(),
                }),
            );

            Operand::Place(Place {
                local: result,
                projection: vec![],
            })
        }
        hir::Expr::Switch(hir::Switch {
            discriminator,
            branches,
            default,
        }) => {
            let discriminator_ty = thir.get_expr_ty(*discriminator);
            let discriminator = lower_expr(thir, builder, *discriminator);

            let current_block = builder.block;

            let switch_value = builder.add_local(thir.get_expr_ty(expr).clone());
            let end_block = builder.new_basic_block();

            // Lower all of the branches.
            let targets = branches
                .iter()
                .map(|(target, block)| {
                    // Create a block for the branch.
                    let bb = builder.new_basic_block();
                    builder.block = bb;

                    // Lower the block.
                    let result = lower_block(thir, builder, thir.get_block(*block));

                    // Store the resulting block value in the switch value, and jump back to merge
                    // block.
                    builder.store(switch_value, RValue::Use(result));
                    builder.goto(end_block);

                    (literal_to_constant(target, discriminator_ty), bb)
                })
                .collect();

            let otherwise = if let Some(default) = default {
                // Create a block.
                let bb = builder.new_basic_block();
                builder.block = bb;

                // Lower the block.
                let result = lower_block(thir, builder, thir.get_block(*default));

                // Store the resulting block value in the switch value, and jump back to merge
                // block.
                builder.store(switch_value, RValue::Use(result));
                builder.goto(end_block);

                bb
            } else {
                end_block
            };

            // Return to the starting block, and add the switch terminator.
            builder.block = current_block;
            builder.switch(discriminator, targets, otherwise);

            builder.block = end_block;

            Operand::Place(Place {
                local: switch_value,
                projection: Vec::new(),
            })
        }
        hir::Expr::Literal(literal) => {
            Operand::Constant(literal_to_constant(literal, thir.get_expr_ty(expr)))
        }
        hir::Expr::Call(call) => todo!(),
        hir::Expr::Block(block_id) => lower_block(thir, builder, thir.get_block(*block_id)),
        hir::Expr::Variable(hir::Variable { binding }) => Operand::Place(Place {
            local: builder[*binding],
            projection: vec![],
        }),
    }
}

struct Builder {
    mir: Mir,
}

impl Builder {
    pub fn new() -> Self {
        Self { mir: Mir::new() }
    }

    pub fn new_basic_block(&mut self) -> BasicBlockId {
        let id = BasicBlockId::new(self.mir.basic_blocks.len());
        self.mir.basic_blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator::Unterminated,
        });
        id
    }

    pub fn function(&mut self, function: &hir::Function) -> FunctionBuilder<'_> {
        FunctionBuilder::new(self, function)
    }

    pub fn build(self) -> Mir {
        self.mir
    }
}

struct FunctionBuilder<'b> {
    builder: &'b mut Builder,
    function_i: usize,
    bindings: HashMap<hir::BindingId, (LocalId, bool)>,
    block: BasicBlockId,
}

impl<'b> FunctionBuilder<'b> {
    fn new(builder: &'b mut Builder, function: &hir::Function) -> Self {
        let entry = builder.new_basic_block();

        let mut bindings = HashMap::new();
        let mut locals = Vec::new();

        // First local is the return value.
        locals.push(function.return_ty.clone());

        // Add a local for each parameter, and register it against the binding.
        for (i, (binding, ty)) in function.parameters.iter().enumerate() {
            locals.push(ty.clone());
            bindings.insert(*binding, (LocalId::new(i), true));
        }

        let function_i = builder.mir.functions.len();

        // Register the function definition.
        builder.mir.functions.push(Function { locals, entry });

        Self {
            builder,
            function_i,
            bindings,
            block: entry,
        }
    }

    fn current_block(&mut self) -> &mut BasicBlock {
        let block = self.block;
        &mut self[block]
    }

    fn function(&mut self) -> &mut Function {
        let i = self.function_i;
        &mut self.mir.functions[i]
    }

    fn add_binding(&mut self, binding: hir::BindingId, ty: Type) -> LocalId {
        let local = self.add_local(ty);
        self.bindings.insert(binding, (local, false));
        local
    }

    fn add_local(&mut self, ty: Type) -> LocalId {
        let locals = &mut self.function().locals;
        let id = LocalId::new(locals.len());
        locals.push(ty);
        id
    }

    fn store(&mut self, local: LocalId, rvalue: RValue) {
        self.assign(
            Place {
                local,
                projection: vec![],
            },
            rvalue,
        );
    }

    fn assign(&mut self, place: Place, rvalue: RValue) {
        self.current_block()
            .statements
            .push(Statement::Assign(Assign { place, rvalue }));
    }

    fn switch(
        &mut self,
        discriminator: Operand,
        targets: Vec<(Constant, BasicBlockId)>,
        otherwise: BasicBlockId,
    ) {
        self.terminate(Terminator::SwitchInt(SwitchInt {
            discriminator,
            targets,
            otherwise,
        }));
    }

    fn goto(&mut self, basic_block: BasicBlockId) {
        self.terminate(Terminator::Goto(Goto { basic_block }));
    }

    fn terminate(&mut self, terminator: Terminator) {
        self.current_block().terminator = terminator;
    }
}

impl Index<BasicBlockId> for FunctionBuilder<'_> {
    type Output = BasicBlock;

    fn index(&self, index: BasicBlockId) -> &Self::Output {
        &self.mir.basic_blocks[index.0]
    }
}

impl IndexMut<BasicBlockId> for FunctionBuilder<'_> {
    fn index_mut(&mut self, index: BasicBlockId) -> &mut Self::Output {
        &mut self.mir.basic_blocks[index.0]
    }
}

impl Index<hir::BindingId> for FunctionBuilder<'_> {
    type Output = LocalId;

    fn index(&self, index: hir::BindingId) -> &Self::Output {
        &self.bindings[&index].0
    }
}

impl Deref for FunctionBuilder<'_> {
    type Target = Builder;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl DerefMut for FunctionBuilder<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder
    }
}

fn literal_to_constant(literal: &hir::Literal, ty: &Type) -> Constant {
    match (literal, ty) {
        (hir::Literal::Integer(value), Type::I8) => Constant::I8(*value as i8),
        (hir::Literal::Integer(value), Type::U8) => Constant::U8(*value as u8),
        (hir::Literal::Boolean(value), Type::Boolean) => Constant::Boolean(*value),
        (hir::Literal::Unit, Type::Unit) => Constant::Unit,
        (literal, ty) => panic!("invalid literal {literal:?} for type {ty:?}"),
    }
}

fn expr_to_place(thir: &Thir, builder: &mut FunctionBuilder<'_>, expr: hir::ExprId) -> Place {
    match thir.get_expr(expr) {
        hir::Expr::Variable(hir::Variable { binding }) => Place {
            local: builder[*binding],
            projection: Vec::new(),
        },
        hir::Expr::Unary(hir::Unary {
            op: UnaryOp::Deref(_),
            value,
        }) => {
            let mut value = expr_to_place(thir, builder, *value);
            // TODO: Not sure if this is append or prepend.
            value.projection.push(Projection::Deref);
            value
        }
        expr => panic!("invalid lhs: {expr:?}"),
    }
}
