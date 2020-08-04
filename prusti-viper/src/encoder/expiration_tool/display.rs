use std::fmt;

use super::ExpirationTool;

impl<'tcx> fmt::Display for ExpirationTool<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "expiration_tool:")?;
        let blocking = (&self.blocking).join_to_string(", ", |b| format!("{:?}", b));
        writeln!(f, "  blocking: {}", blocking)?;
        let blocked = (&self.blocked).join_to_string(", ", |b| format!("{:?}", b));
        writeln!(f, "  blocked: {}", blocked)?;
        writeln!(f, "  magic_wands:")?;
        for magic_wand in &self.magic_wands {
            writeln!(f, "   - expired: {:?}", magic_wand.expired())?;
            let unblocked = (&magic_wand.unblocked).join_to_string(", ", |u| format!("{:?}", u));
            writeln!(f, "     unblocked: {:?}", unblocked)?;
            writeln!(f, "     pledges:")?;
            for pledge in magic_wand.pledges() {
                writeln!(f, "      - {:?}", pledge)?;
            }
            for expiration_tool in &magic_wand.expiration_tools {
                let expiration_tool = format!("{}", expiration_tool);
                for line in expiration_tool.lines() {
                    writeln!(f, "     {}", line)?;
                }
            }
        }
        Ok(())
    }
}

pub trait MapToString<T> {
    fn join_to_string(self, sep: &str, f: impl Fn(T) -> String) -> String;
}

impl<'a, T, R: IntoIterator<Item=T>> MapToString<T> for R {
    fn join_to_string(self, sep: &str, f: impl Fn(T) -> String) -> String {
        self.into_iter().map(f).collect::<Vec<_>>().join(sep)
    }
}
