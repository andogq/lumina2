use crate::{
    Ctx,
    lex::Lexer,
    passes::{Pass, PassResult, PassSuccess},
};

pub struct TokGen;

impl<'ctx, 'src> Pass<'ctx, 'src> for TokGen {
    type Input = str;
    type Output = Lexer<'src>;

    fn run(_ctx: &'ctx mut Ctx, src: &'src Self::Input) -> super::PassResult<Self::Output> {
        PassResult::Ok(PassSuccess::Ok(Lexer::new(src)))
    }
}
