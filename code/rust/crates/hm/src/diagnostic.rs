//! Error messages in the style of rustc: a headline, the offending source
//! line with the culprit underlined, and notes that explain why.
//!
//! ```text
//! error: mismatched types
//!  --> example:1:30
//!   |
//! 1 | fun id -> if id true then id 1 else 2
//!   |                              ^ expected `Bool`, found `Int`
//!   |
//!   = note: ...
//! ```

use crate::syntax::Span;

/// A message attached to a span. The primary label (underlined with `^`)
/// marks the culprit; secondary labels (underlined with `-`) give context.
#[derive(Clone, Debug, PartialEq)]
pub struct Label {
    pub span: Span,
    pub text: String,
    pub primary: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Diagnostic {
    pub message: String,
    pub labels: Vec<Label>,
    /// Lines printed after the snippet, as `= note: ...` or `= help: ...`.
    pub notes: Vec<(&'static str, String)>,
}

impl Diagnostic {
    pub fn error(message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            message: message.into(),
            labels: vec![],
            notes: vec![],
        }
    }

    pub fn primary(mut self, span: Span, text: impl Into<String>) -> Diagnostic {
        self.labels.push(Label {
            span,
            text: text.into(),
            primary: true,
        });
        self
    }

    pub fn secondary(mut self, span: Span, text: impl Into<String>) -> Diagnostic {
        self.labels.push(Label {
            span,
            text: text.into(),
            primary: false,
        });
        self
    }

    pub fn note(mut self, text: impl Into<String>) -> Diagnostic {
        self.notes.push(("note", text.into()));
        self
    }

    pub fn help(mut self, text: impl Into<String>) -> Diagnostic {
        self.notes.push(("help", text.into()));
        self
    }

    /// Renders the diagnostic against the source it refers to. `name` is
    /// shown in the location line, like a file name.
    pub fn render(&self, name: &str, source: &str) -> String {
        let lines: Vec<&str> = source.split('\n').collect();
        let mut by_line: Vec<(usize, Vec<&Label>)> = Vec::new();
        for label in &self.labels {
            let (line, _) = line_col(source, label.span.start);
            match by_line.iter_mut().find(|(l, _)| *l == line) {
                Some((_, group)) => group.push(label),
                None => by_line.push((line, vec![label])),
            }
        }
        by_line.sort_by_key(|(line, _)| *line);
        let last_line = by_line.iter().map(|(l, _)| *l).max().unwrap_or(1);
        let width = last_line.to_string().len();
        let pad = " ".repeat(width);

        let mut out = format!("error: {}\n", self.message);
        let primary = self
            .labels
            .iter()
            .find(|l| l.primary)
            .or(self.labels.first());
        if let Some(label) = primary {
            let (line, col) = line_col(source, label.span.start);
            out += &format!("{pad}--> {name}:{line}:{col}\n");
        }
        if !by_line.is_empty() {
            out += &format!("{pad} |\n");
        }
        for (line, group) in &by_line {
            let text = lines[line - 1];
            out += &format!("{line:>width$} | {text}\n");
            for marker_line in render_labels(source, text, group) {
                out += &format!("{pad} |{marker_line}\n");
            }
        }
        if !self.notes.is_empty() {
            out += &format!("{pad} |\n");
        }
        for (kind, note) in &self.notes {
            out += &format!("{pad} = {kind}: {note}\n");
        }
        out
    }
}

/// The 1-based line and column (in characters) of a byte offset.
pub fn line_col(source: &str, offset: usize) -> (usize, usize) {
    let before = &source[..offset.min(source.len())];
    let line = before.matches('\n').count() + 1;
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let col = source[line_start..offset.min(source.len())].chars().count() + 1;
    (line, col)
}

/// The marker lines under one source line: underlines for every label, the
/// rightmost label's text on the same line, the others hanging below on
/// vertical bars (the layout rustc uses).
fn render_labels(source: &str, line_text: &str, group: &[&Label]) -> Vec<String> {
    // Column (0-based, in characters) and width of each underline.
    let mut marks: Vec<(usize, usize, &Label)> = group
        .iter()
        .map(|label| {
            let (_, col) = line_col(source, label.span.start);
            let start = col - 1;
            let line_len = line_text.chars().count();
            let span_chars = source[label.span.start..label.span.end].chars().count();
            let width = span_chars.min(line_len.saturating_sub(start)).max(1);
            (start, width, *label)
        })
        .collect();
    marks.sort_by_key(|(start, _, _)| *start);

    let mut underline: Vec<char> = Vec::new();
    for &(start, width, label) in &marks {
        if underline.len() < start + width {
            underline.resize(start + width, ' ');
        }
        for slot in &mut underline[start..start + width] {
            if label.primary || *slot == ' ' {
                *slot = if label.primary { '^' } else { '-' };
            }
        }
    }
    let mut first = format!(" {}", underline.iter().collect::<String>());
    let (rightmost, rest) = marks.split_last().expect("at least one label");
    if !rightmost.2.text.is_empty() {
        first += &format!(" {}", rightmost.2.text);
    }
    let mut out = vec![first.trim_end().to_string()];

    // The other labels, from right to left, each on a vertical bar.
    let hanging: Vec<&(usize, usize, &Label)> =
        rest.iter().filter(|(_, _, l)| !l.text.is_empty()).collect();
    for (i, &&(col, _, label)) in hanging.iter().enumerate().rev() {
        let bars = |upto: usize| {
            let mut row = vec![' '; col + 1];
            for &&(c, _, _) in &hanging[..upto] {
                row[c] = '|';
            }
            row
        };
        let mut connector = bars(i);
        connector[col] = '|';
        out.push(
            format!(" {}", connector.iter().collect::<String>())
                .trim_end()
                .to_string(),
        );
        let mut text_row: String = bars(i)[..col].iter().collect();
        text_row += &label.text;
        out.push(format!(" {text_row}"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_label() {
        let src = "if 1 then 2 else 3";
        let d = Diagnostic::error("mismatched types")
            .primary(Span::new(3, 4), "expected `Bool`, found `Int`")
            .note("the condition of an `if` must be a `Bool`");
        let expected = "\
error: mismatched types
 --> t:1:4
  |
1 | if 1 then 2 else 3
  |    ^ expected `Bool`, found `Int`
  |
  = note: the condition of an `if` must be a `Bool`
";
        assert_eq!(d.render("t", src), expected);
    }

    #[test]
    fn secondary_label_hangs_below() {
        let src = "if b then 1 else true";
        let d = Diagnostic::error("`if` and `else` have incompatible types")
            .primary(Span::new(17, 21), "expected `Int`, found `Bool`")
            .secondary(Span::new(10, 11), "expected because of this");
        let expected = "\
error: `if` and `else` have incompatible types
 --> t:1:18
  |
1 | if b then 1 else true
  |           -      ^^^^ expected `Int`, found `Bool`
  |           |
  |           expected because of this
";
        assert_eq!(d.render("t", src), expected);
    }

    #[test]
    fn line_and_column() {
        assert_eq!(line_col("ab\ncd", 4), (2, 2));
        assert_eq!(line_col("ab\ncd", 0), (1, 1));
    }
}
