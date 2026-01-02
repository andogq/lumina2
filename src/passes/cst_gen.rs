use crate::{prelude::*, stages::parse::Parse};

pub struct CstGen;
impl<'ctx, 'src> Pass<'ctx, 'src> for CstGen {
    type Input = str;
    type Output = cst::Program;
    type Extra = ();

    fn run(_ctx: &'ctx mut Ctx, src: &'src str, _extra: ()) -> PassResult<Self::Output> {
        let mut lexer = Lexer::new(src);
        Ok(PassSuccess::Ok(cst::Program::parse(&mut lexer)))
    }
}
