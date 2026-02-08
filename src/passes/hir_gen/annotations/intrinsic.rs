use crate::prelude::*;

use super::*;

pub fn intrinsic_handler(ctx: &mut Ctx, hir: &mut hir::Hir, hir_node: HirId) {
    let HirNodePtr::Function(hir_node) = hir[hir_node] else {
        panic!("only functions support `@intrinsic`");
    };

    let node = &hir[hir_node];
    assert!(
        node.entry.is_none(),
        "functions with `intrinsic` annotation cannot have an implementation"
    );

    // Find matching intrinsic.
    let target_intrinsic = ctx.strings.get(ctx.scopes.to_string(node.binding));
    let Some(intrinsic) = INTRINSICS
        .iter()
        .find(|intrinsic| intrinsic.name == target_intrinsic)
    else {
        panic!("could not find intrinsic: {target_intrinsic}");
    };

    // Validate signature.
    let hir_signature = &hir[hir_node].signature;
    let signature_valid =
            // Parameter counts must match.
            hir_signature.parameters.len() == intrinsic.signature.parameters.len()
            // Each parameter must match.
            && intrinsic
                .signature
                .parameters
                .iter()
                .zip(hir_signature.parameters.iter().map(|(_, ty)| *ty))
                .all(|(intrinsic, signature)| intrinsic.as_type(&mut ctx.types) == signature)
            // Return type must match.
            && intrinsic
                .signature
                .return_ty
                .as_ref()
                .map(|ty| ty.as_type(&mut ctx.types))
                .unwrap_or(ctx.types.unit())
            == hir_signature.return_ty;
    if !signature_valid {
        panic!("intrinsic signature mismatch");
    }

    // Generate an implementation for the body.
    let expression = match &intrinsic.implementation {
        IntrinsicImplementation::UnaryOperation(unary_operation) => {
            assert_eq!(
                intrinsic.signature.parameters.len(),
                1,
                "unary intrinsic must only accept one parameter"
            );

            // Create an expression referencing the parameter.
            let value = hir.add_expression(hir::Variable {
                binding: hir_signature.parameters[0].0,
            });

            // Apply unary operation to parameter.
            hir.add_expression(hir::Unary {
                operation: *unary_operation,
                value,
            })
        }
        IntrinsicImplementation::BinaryOperation(binary_operation) => {
            assert_eq!(
                intrinsic.signature.parameters.len(),
                2,
                "binary intrinsic must only accept two parameters"
            );

            // Create expressions for each parameter.
            let [lhs, rhs] = [hir_signature.parameters[0].0, hir_signature.parameters[1].0]
                .map(|binding| hir.add_expression(hir::Variable { binding }));

            // Apply binary operation to parameters.
            hir.add_expression(hir::Binary {
                lhs,
                operation: *binary_operation,
                rhs,
            })
        }
    };

    // Update the body of the HIR node.
    let entry = hir.add_block(vec![], expression);
    hir[hir_node].entry = Some(entry);
}

#[derive(Clone, Debug)]
pub struct Intrinsic {
    name: &'static str,
    implementation: IntrinsicImplementation,
    signature: Signature,
}

#[derive(Clone, Debug)]
pub struct Signature {
    parameters: &'static [PrimitiveType],
    return_ty: Option<PrimitiveType>,
}

#[derive(Clone, Debug)]
enum PrimitiveType {
    U8,
    I8,
    Boolean,
    Tuple(&'static [PrimitiveType]),
}

impl PrimitiveType {
    fn as_type(&self, types: &mut Types) -> TypeId {
        match self {
            PrimitiveType::U8 => types.u8(),
            PrimitiveType::I8 => types.i8(),
            PrimitiveType::Boolean => types.boolean(),
            PrimitiveType::Tuple(primitive_types) => {
                let inner = primitive_types
                    .iter()
                    .map(|ty| ty.as_type(types))
                    .collect::<Vec<_>>();
                types.tuple(inner)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum IntrinsicImplementation {
    UnaryOperation(UnaryOperation),
    BinaryOperation(BinaryOperation),
}

macro_rules! intrinsics {
    (@return_type) => {
        None
    };

    (@return_type $return_type:tt) => {
        Some(intrinsics!(@type $return_type))
    };

    (@type u8) => {
        PrimitiveType::U8
    };

    (@type i8) => {
        PrimitiveType::I8
    };

    (@type bool) => {
        PrimitiveType::Boolean
    };

    (@type ($($ty:tt),* $(,)?)) => {
        PrimitiveType::Tuple(&[
            $(intrinsics!(@type $ty)),*
        ])
    };

    (@type $ty:tt) => {
        compile_error!(stringify!($ty))
    };

    (
        @intrinsics
        [$($complete:tt)*]
        // spell-checker: disable-next-line
        $name:ident ($($parameter_name:ident: $parameter_type:tt),* $(,)?) $(-> $return_type:tt)? { $implementation:expr };
        $($rest:tt)*
    ) => {
        intrinsics!(
            @intrinsics
            [
                $($complete)*
                Intrinsic {
                    name: stringify!($name),
                    implementation: $implementation,
                    signature: Signature {
                        parameters: &[$(intrinsics!(@type $parameter_type),)*],
                        return_ty: intrinsics!(@return_type $($return_type)?),
                    },
                },
            ]
            $($rest)*
        );
    };

    (@intrinsics [$($complete:tt)*]) => {
        const INTRINSICS: &'static [Intrinsic] = {
            #[allow(unused_imports, reason = "macro expansion")]
            use self::{
                IntrinsicImplementation::*,
                BinaryOperation::*,
                UnaryOperation::*,
            };

            &[
                $($complete)*
            ]
        };
    };

    ($($toks:tt)*) => {
        intrinsics!(@intrinsics [] $($toks)*);
    };
}

intrinsics! {
    u8_add_wrapping(lhs: u8, rhs: u8) -> u8 { BinaryOperation(Plus) };
    u8_add_overflow(lhs: u8, rhs: u8) -> (u8, bool) { BinaryOperation(PlusWithOverflow) };
    u8_not(n: u8) -> u8 { UnaryOperation(Not) };

    i8_add_wrapping(lhs: i8, rhs: i8) -> i8 { BinaryOperation(Plus) };
    i8_add_overflow(lhs: i8, rhs: i8) -> (i8, bool) { BinaryOperation(PlusWithOverflow) };
    i8_not(n: i8) -> i8 { UnaryOperation(Not) };
}
