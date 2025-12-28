use crate::prelude::*;

use cst::UnaryOp;
use hir::{Thir, Type};
use mir::*;

pub fn lower(thir: &Thir) -> Mir {
    let mut builder = Builder::new();

    for function in thir.functions.iter_keys() {
        lower_function(thir, &mut builder, function);
    }

    builder.build()
}

fn lower_function(thir: &Thir, builder: &mut Builder, function: hir::FunctionId) {
    let function = &thir[function];
    let mut builder = builder.function(
        function,
        thir.functions.iter_pairs().map(|(id, f)| {
            (
                f.binding,
                // HACK: Properly pre-declare functions.
                FunctionId::from_id(id.into_id()),
            )
        }),
    );

    let block = &thir[function.entry];
    let result = lower_block(thir, &mut builder, block);

    // If the block resolves to a value of the same type as the return value, then it's an implicit
    // return.
    if let Some(result) = result
        && thir.type_of(block.expr) == &function.return_ty
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
    builder: &mut FunctionBuilder<'_>,
    block: &hir::Block,
) -> Option<Operand> {
    for statement in &block.statements {
        match &thir[*statement] {
            hir::Statement::Declare(hir::DeclareStatement { binding, ty }) => {
                builder.add_binding(
                    *binding,
                    match ty {
                        hir::DeclarationTy::Type(ty) => ty,
                        hir::DeclarationTy::Inferred(expr) => thir.type_of(*expr),
                    }
                    .clone(),
                );
            }
            hir::Statement::Return(hir::ReturnStatement { expr }) => {
                if let Some(value) = lower_expr(thir, builder, *expr) {
                    builder.store(LocalId::new(0), RValue::Use(value));
                }
                builder.terminate(Terminator::Return);
            }
            hir::Statement::Expr(hir::ExprStatement { expr }) => {
                lower_expr(thir, builder, *expr);
            }
        }
    }

    lower_expr(thir, builder, block.expr)
}

fn lower_expr(
    thir: &Thir,
    builder: &mut FunctionBuilder<'_>,
    expr: hir::ExprId,
) -> Option<Operand> {
    Some(match &thir[expr] {
        hir::Expr::Assign(hir::Assign { variable, value }) => {
            let value = lower_expr(thir, builder, *value)?;
            let place = expr_to_place(thir, builder, *variable);
            builder.assign(place, RValue::Use(value));

            Operand::Constant(Constant::Unit)
        }
        hir::Expr::Binary(hir::Binary { lhs, op, rhs }) => {
            let lhs = lower_expr(thir, builder, *lhs)?;
            let rhs = lower_expr(thir, builder, *rhs)?;

            let result = builder.add_local(None, thir.type_of(expr).clone());

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
            let value = lower_expr(thir, builder, *value)?;

            let result = builder.add_local(None, thir.type_of(expr).clone());

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
            let discriminator_ty = thir.type_of(*discriminator);
            let discriminator = lower_expr(thir, builder, *discriminator)?;

            let current_block = builder.block;

            let switch_ty = thir.type_of(expr);
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
                    if let Some(result) = lower_block(thir, builder, &thir[*block])
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
                let result = lower_block(thir, builder, &thir[*default])?;

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
            Operand::Constant(literal_to_constant(literal, thir.type_of(expr)))
        }
        hir::Expr::Call(call) => {
            let result = Place {
                local: builder.add_local(None, thir.type_of(expr).clone()),
                projection: Vec::new(),
            };
            let target = builder.new_basic_block();

            let func = lower_expr(thir, builder, call.callee).unwrap();
            let args = call
                .arguments
                .iter()
                .map(|expr| lower_expr(thir, builder, *expr).unwrap())
                .collect();
            builder.call(func, args, result.clone(), target);

            builder.block = target;

            Operand::Place(result)
        }
        hir::Expr::Block(block_id) => lower_block(thir, builder, &thir[*block_id])?,
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

    pub fn function(
        &mut self,
        function: &hir::Function,
        functions: impl Iterator<Item = (BindingId, FunctionId)>,
    ) -> FunctionBuilder<'_> {
        FunctionBuilder::new(self, function, functions)
    }

    pub fn build(self) -> Mir {
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
    function: FunctionId,
    bindings: HashMap<BindingId, (Binding, bool)>,
    block: BasicBlockId,
}

impl<'b> FunctionBuilder<'b> {
    fn new(
        builder: &'b mut Builder,
        function: &hir::Function,
        functions: impl Iterator<Item = (BindingId, FunctionId)>,
    ) -> Self {
        let (bindings, locals) = {
            let mut bindings = HashMap::new();
            let mut locals = Vec::new();

            // Add bindings for function declarations.
            bindings
                .extend(functions.map(|(binding, id)| (binding, (Binding::Function(id), false))));

            // First local is the return value.
            locals.push((None, function.return_ty.clone()));

            // Add a local for each parameter, and register it against the binding.
            for (binding, ty) in function.parameters.iter() {
                let i = locals.len();
                locals.push((Some(*binding), ty.clone()));
                bindings.insert(*binding, (Binding::Local(LocalId::new(i)), true));
            }

            (bindings, locals)
        };

        let temp_entry = BasicBlockId::new(0);

        // Register the function definition.
        let function_id = builder.mir.functions.insert(Function {
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

        let mut builder = Self {
            builder,
            function: function_id,
            bindings,
            // Temporary value for the current block,
            block: temp_entry,
        };

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
        &self.mir[self.function]
    }

    fn function_mut(&mut self) -> &mut Function {
        let id = self.function;
        &mut self.mir[id]
    }

    pub fn new_basic_block(&mut self) -> BasicBlockId {
        let id = BasicBlockId::new(self.function().basic_blocks.len());
        self.function_mut().basic_blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator::Unterminated,
        });
        id
    }

    fn add_binding(&mut self, binding: BindingId, ty: Type) -> LocalId {
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

impl Index<BindingId> for FunctionBuilder<'_> {
    type Output = Binding;

    fn index(&self, index: BindingId) -> &Self::Output {
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
    match &thir[expr] {
        hir::Expr::Variable(hir::Variable { binding }) => Place {
            local: *builder[*binding].as_local(),
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
