use std::{
    collections::HashMap,
    ops::{Deref, DerefMut, Index, IndexMut},
};

use crate::ir::{
    ast::{StringId, StringPool},
    cst::UnaryOp,
    hir::{self, BindingId, Thir, Type, thir},
    mir::*,
};

pub fn lower(thir: &Thir) -> Mir {
    let mut builder = Builder::new();

    for function in &thir.functions {
        lower_function(thir, &mut builder, function);
    }

    builder.build(thir.strings.clone(), thir.binding_to_string.clone())
}

fn lower_function(thir: &Thir, builder: &mut Builder, function: &thir::Function) {
    let mut builder = builder.function(function);

    let block = function.get_block(function.entry);
    let result = lower_block(thir, function, &mut builder, block);

    // If the block resolves to a value of the same type as the return value, then it's an implicit
    // return.
    if let Some(result) = result
        && function.get_expr_ty(block.expr) == &function.return_ty
    {
        builder.store(LocalId::new(0), RValue::Use(result));
    }

    // Function block must always terminate with a return.
    if matches!(builder.current_block().terminator, Terminator::Unterminated) {
        builder.terminate(Terminator::Return);
    }
}

fn lower_block(
    thir: &Thir,
    function: &thir::Function,
    builder: &mut FunctionBuilder<'_>,
    block: &hir::Block,
) -> Option<Operand> {
    for statement in &block.statements {
        match statement {
            hir::Statement::Declare(hir::DeclareStatement { binding, ty }) => {
                builder.add_binding(
                    *binding,
                    match ty {
                        hir::DeclarationTy::Type(ty) => ty,
                        hir::DeclarationTy::Inferred(expr) => function.get_expr_ty(*expr),
                    }
                    .clone(),
                );
            }
            hir::Statement::Return(hir::ReturnStatement { expr }) => {
                if let Some(value) = lower_expr(thir, function, builder, *expr) {
                    builder.store(LocalId::new(0), RValue::Use(value));
                }
                builder.terminate(Terminator::Return);
            }
            hir::Statement::Expr(hir::ExprStatement { expr }) => {
                lower_expr(thir, function, builder, *expr);
            }
        }
    }

    lower_expr(thir, function, builder, block.expr)
}

fn lower_expr(
    thir: &Thir,
    function: &thir::Function,
    builder: &mut FunctionBuilder<'_>,
    expr: hir::ExprId,
) -> Option<Operand> {
    Some(match function.get_expr(expr) {
        hir::Expr::Assign(hir::Assign { variable, value }) => {
            let value = lower_expr(thir, function, builder, *value)?;
            let place = expr_to_place(thir, function, builder, *variable);
            builder.assign(place, RValue::Use(value));

            Operand::Constant(Constant::Unit)
        }
        hir::Expr::Binary(hir::Binary { lhs, op, rhs }) => {
            let lhs = lower_expr(thir, function, builder, *lhs)?;
            let rhs = lower_expr(thir, function, builder, *rhs)?;

            let result = builder.add_local(None, function.get_expr_ty(expr).clone());

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
            let value = lower_expr(thir, function, builder, *value)?;

            let result = builder.add_local(None, function.get_expr_ty(expr).clone());

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
            let discriminator_ty = function.get_expr_ty(*discriminator);
            let discriminator = lower_expr(thir, function, builder, *discriminator)?;

            let current_block = builder.block;

            let switch_ty = function.get_expr_ty(expr);
            let switch_value = builder.add_local(None, switch_ty.clone());
            let end_block = builder.new_basic_block();

            // Lower all of the branches.
            let targets = branches
                .iter()
                .map(|(target, block)| {
                    // Create a block for the branch.
                    let bb = builder.new_basic_block();
                    builder.block = bb;

                    // Lower the block.
                    if let Some(result) =
                        lower_block(thir, function, builder, function.get_block(*block))
                        && !matches!(switch_ty, Type::Unit | Type::Never)
                    {
                        // Store the resulting block value in the switch value, and jump back to merge
                        // block.
                        builder.store(switch_value, RValue::Use(result));
                    }

                    // Jump back to the end block, if it hasn't been terminated.
                    if matches!(builder.current_block().terminator, Terminator::Unterminated) {
                        builder.goto(end_block);
                    }

                    (literal_to_constant(target, discriminator_ty), bb)
                })
                .collect();

            let otherwise = if let Some(default) = default {
                // Create a block.
                let bb = builder.new_basic_block();
                builder.block = bb;

                // Lower the block.
                let result = lower_block(thir, function, builder, function.get_block(*default))?;

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
            Operand::Constant(literal_to_constant(literal, function.get_expr_ty(expr)))
        }
        hir::Expr::Call(call) => {
            let result = Place {
                local: builder.add_local(None, function.get_expr_ty(expr).clone()),
                projection: Vec::new(),
            };
            let target = builder.new_basic_block();

            let func = lower_expr(thir, function, builder, call.callee).unwrap();
            let args = call
                .arguments
                .iter()
                .map(|expr| lower_expr(thir, function, builder, *expr).unwrap())
                .collect();
            builder.call(func, args, result.clone(), target);

            builder.block = target;

            Operand::Place(result)
        }
        hir::Expr::Block(block_id) => {
            lower_block(thir, function, builder, function.get_block(*block_id))?
        }
        hir::Expr::Variable(hir::Variable { binding }) => match builder[*binding] {
            Binding::Local(local) => Operand::Place(Place {
                local,
                projection: vec![],
            }),
            Binding::Function(function_id) => Operand::Constant(Constant::Function(function_id)),
        },
        hir::Expr::Unreachable => return None,
    })
}

struct Builder {
    mir: Mir,
}

impl Builder {
    pub fn new() -> Self {
        Self { mir: Mir::new() }
    }

    pub fn function(&mut self, function: &thir::Function) -> FunctionBuilder<'_> {
        FunctionBuilder::new(self, function)
    }

    pub fn build(
        mut self,
        strings: StringPool,
        binding_to_string: HashMap<BindingId, StringId>,
    ) -> Mir {
        self.mir.strings = strings;
        self.mir.binding_to_string = binding_to_string;
        self.mir
    }
}

enum Binding {
    Local(LocalId),
    Function(FunctionId),
}

impl Binding {
    pub fn into_local(self) -> LocalId {
        match self {
            Self::Local(local) => local,
            _ => panic!(),
        }
    }

    pub fn into_function(self) -> FunctionId {
        match self {
            Self::Function(function_id) => function_id,
            _ => panic!(),
        }
    }

    pub fn as_local(&self) -> &LocalId {
        match self {
            Self::Local(local) => local,
            _ => panic!(),
        }
    }

    pub fn as_function(&self) -> &FunctionId {
        match self {
            Self::Function(function_id) => function_id,
            _ => panic!(),
        }
    }
}

struct FunctionBuilder<'b> {
    builder: &'b mut Builder,
    function_i: usize,
    bindings: HashMap<hir::BindingId, (Binding, bool)>,
    block: BasicBlockId,
}

impl<'b> FunctionBuilder<'b> {
    fn new(builder: &'b mut Builder, function: &thir::Function) -> Self {
        let (bindings, locals) =
            {
                let mut bindings = HashMap::new();
                let mut locals = Vec::new();

                // Add bindings for function declarations.
                bindings.extend(
                    builder.mir.functions.iter().enumerate().map(|(id, f)| {
                        (f.binding, (Binding::Function(FunctionId::new(id)), false))
                    }),
                );

                // First local is the return value.
                locals.push((None, function.return_ty.clone()));

                // Add a local for each parameter, and register it against the binding.
                for (i, (binding, ty)) in function.parameters.iter().enumerate() {
                    locals.push((Some(*binding), ty.clone()));
                    bindings.insert(*binding, (Binding::Local(LocalId::new(i)), true));
                }

                (bindings, locals)
            };

        let temp_entry = BasicBlockId::new(0);

        let function_i = builder.mir.functions.len();
        let mut builder = Self {
            builder,
            function_i,
            bindings,
            // Temporary value for the current block,
            block: temp_entry,
        };

        // Register the function definition.
        builder.mir.functions.push(Function {
            binding: function.binding,
            locals,
            entry: temp_entry,
            ret_ty: function.return_ty.clone(),
            params: function
                .parameters
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect(),
            basic_blocks: Vec::new(),
        });

        // Actually create the entry basic block.
        let entry = builder.new_basic_block();
        builder.block = entry;
        builder.function_mut().entry = entry;

        builder
    }

    fn current_block(&mut self) -> &mut BasicBlock {
        let block = self.block;
        &mut self[block]
    }

    fn function(&self) -> &Function {
        let i = self.function_i;
        &self.mir.functions[i]
    }

    fn function_mut(&mut self) -> &mut Function {
        let i = self.function_i;
        &mut self.mir.functions[i]
    }

    pub fn new_basic_block(&mut self) -> BasicBlockId {
        let id = BasicBlockId::new(self.function().basic_blocks.len());
        self.function_mut().basic_blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator::Unterminated,
        });
        id
    }

    fn add_binding(&mut self, binding: hir::BindingId, ty: Type) -> LocalId {
        let local = self.add_local(Some(binding), ty);
        self.bindings
            .insert(binding, (Binding::Local(local), false));
        local
    }

    fn add_local(&mut self, binding: Option<BindingId>, ty: Type) -> LocalId {
        let locals = &mut self.function_mut().locals;
        let id = LocalId::new(locals.len());
        locals.push((binding, ty));
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

    fn call(
        &mut self,
        func: Operand,
        args: Vec<Operand>,
        destination: Place,
        target: BasicBlockId,
    ) {
        self.terminate(Terminator::Call(Call {
            func,
            args,
            destination,
            target,
        }));
    }

    fn terminate(&mut self, terminator: Terminator) {
        self.current_block().terminator = terminator;
    }
}

impl Index<BasicBlockId> for FunctionBuilder<'_> {
    type Output = BasicBlock;

    fn index(&self, index: BasicBlockId) -> &Self::Output {
        &self.function().basic_blocks[index.0]
    }
}

impl IndexMut<BasicBlockId> for FunctionBuilder<'_> {
    fn index_mut(&mut self, index: BasicBlockId) -> &mut Self::Output {
        &mut self.function_mut().basic_blocks[index.0]
    }
}

impl Index<hir::BindingId> for FunctionBuilder<'_> {
    type Output = Binding;

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

fn expr_to_place(
    thir: &Thir,
    function: &thir::Function,
    builder: &mut FunctionBuilder<'_>,
    expr: hir::ExprId,
) -> Place {
    match function.get_expr(expr) {
        hir::Expr::Variable(hir::Variable { binding }) => Place {
            local: *builder[*binding].as_local(),
            projection: Vec::new(),
        },
        hir::Expr::Unary(hir::Unary {
            op: UnaryOp::Deref(_),
            value,
        }) => {
            let mut value = expr_to_place(thir, function, builder, *value);
            // TODO: Not sure if this is append or prepend.
            value.projection.push(Projection::Deref);
            value
        }
        expr => panic!("invalid lhs: {expr:?}"),
    }
}
