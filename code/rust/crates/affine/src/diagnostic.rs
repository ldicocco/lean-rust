//! Error messages in the style of rustc: a header with the error code, the
//! location, the source lines with labeled underlines, and notes.

use crate::syntax::Span;

/// An underlined region of the source with a short text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub text: String,
    /// The primary label is underlined with `^`, the others with `-`.
    pub primary: bool,
}

impl Label {
    pub fn primary(span: Span, text: &str) -> Label {
        Label {
            span,
            text: text.to_string(),
            primary: true,
        }
    }

    pub fn secondary(span: Span, text: &str) -> Label {
        Label {
            span,
            text: text.to_string(),
            primary: false,
        }
    }
}

/// A `note:` attached to an error, with its own labeled source lines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubDiagnostic {
    pub message: String,
    pub labels: Vec<Label>,
}

/// An error: `error[code]: message`, labels, `= note:` lines and `note:`
/// sub-diagnostics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: Option<String>,
    pub message: String,
    pub labels: Vec<Label>,
    pub notes: Vec<String>,
    pub children: Vec<SubDiagnostic>,
}

impl Diagnostic {
    /// An error without a code (used for syntax errors).
    pub fn error(message: &str) -> Diagnostic {
        Diagnostic {
            code: None,
            message: message.to_string(),
            labels: Vec::new(),
            notes: Vec::new(),
            children: Vec::new(),
        }
    }

    /// An error with a code such as `E0382`.
    pub fn new(code: &str, message: &str) -> Diagnostic {
        Diagnostic {
            code: Some(code.to_string()),
            ..Diagnostic::error(message)
        }
    }

    pub fn with(mut self, label: Label) -> Diagnostic {
        self.labels.push(label);
        self
    }

    pub fn note(mut self, note: &str) -> Diagnostic {
        self.notes.push(note.to_string());
        self
    }

    pub fn child(mut self, message: &str, label: Label) -> Diagnostic {
        self.children.push(SubDiagnostic {
            message: message.to_string(),
            labels: vec![label],
        });
        self
    }

    /// Render the diagnostic for the source text `src` of the file `file`.
    pub fn render(&self, file: &str, src: &str) -> String {
        let src = Source::new(src);
        // The gutter is as wide as the largest line number shown anywhere.
        let all_labels = self
            .labels
            .iter()
            .chain(self.children.iter().flat_map(|c| c.labels.iter()));
        let width = all_labels
            .map(|l| digits(src.line_col(l.span.start).0))
            .max()
            .unwrap_or(1);
        let mut out = String::new();
        match &self.code {
            Some(code) => out += &format!("error[{code}]: {}\n", self.message),
            None => out += &format!("error: {}\n", self.message),
        }
        render_snippet(&mut out, file, &src, &self.labels, width);
        if !self.notes.is_empty() || !self.children.is_empty() {
            out += &format!("{:width$} |\n", "");
        }
        for note in &self.notes {
            out += &format!("{:width$} = {note}\n", "");
        }
        for child in &self.children {
            out += &format!("note: {}\n", child.message);
            render_snippet(&mut out, file, &src, &child.labels, width);
        }
        out
    }
}

fn digits(n: usize) -> usize {
    n.to_string().len()
}

/// The source text split into lines, to turn byte offsets into positions.
struct Source<'a> {
    lines: Vec<(usize, &'a str)>,
}

impl<'a> Source<'a> {
    fn new(text: &'a str) -> Source<'a> {
        let mut lines = Vec::new();
        let mut start = 0;
        for line in text.split('\n') {
            lines.push((start, line));
            start += line.len() + 1;
        }
        Source { lines }
    }

    /// 1-based line and column of a byte offset.
    fn line_col(&self, offset: usize) -> (usize, usize) {
        let idx = self
            .lines
            .iter()
            .rposition(|(start, _)| *start <= offset)
            .unwrap_or(0);
        let (start, line) = self.lines[idx];
        let col = line[..(offset - start).min(line.len())].chars().count();
        (idx + 1, col + 1)
    }

    fn line(&self, n: usize) -> &'a str {
        self.lines[n - 1].1
    }
}

fn render_snippet(
    out: &mut String,
    file: &str,
    src: &Source,
    labels: &[Label],
    width: usize,
) {
    let Some(primary) = labels.iter().find(|l| l.primary).or(labels.first()) else {
        return;
    };
    let (line, col) = src.line_col(primary.span.start);
    *out += &format!("{:width$}--> {file}:{line}:{col}\n", "");
    *out += &format!("{:width$} |\n", "");
    // Group the labels by line (a label that spans several lines is shown on
    // its first line, underlining up to the end of that line).
    let mut lines: Vec<usize> = labels
        .iter()
        .map(|l| src.line_col(l.span.start).0)
        .collect();
    lines.sort();
    lines.dedup();
    let mut previous: Option<usize> = None;
    for &n in &lines {
        if let Some(p) = previous {
            if n == p + 2 {
                *out += &format!("{:>width$} | {}\n", p + 1, src.line(p + 1));
            } else if n > p + 2 {
                *out += "...\n";
            }
        }
        *out += &format!("{n:>width$} | {}\n", src.line(n));
        let mut marks: Vec<(usize, usize, &Label)> = labels
            .iter()
            .filter(|l| src.line_col(l.span.start).0 == n)
            .map(|l| {
                let (_, c) = src.line_col(l.span.start);
                let (end_line, end_col) = src.line_col(l.span.end);
                let len = if end_line == n {
                    end_col.saturating_sub(c).max(1)
                } else {
                    src.line(n).chars().count().saturating_sub(c - 1).max(1)
                };
                (c - 1, len, l)
            })
            .collect();
        marks.sort_by_key(|m| m.0);
        for row in label_rows(&marks) {
            if row.is_empty() {
                *out += &format!("{:width$} |\n", "");
            } else {
                *out += &format!("{:width$} | {}\n", "", row.trim_end());
            }
        }
        previous = Some(n);
    }
}

/// The rows under one source line: the underlines, with the text of the last
/// label (and of any other label whose text fits before the next underline)
/// on the same row, and the remaining texts below, connected with `|`.
fn label_rows(marks: &[(usize, usize, &Label)]) -> Vec<String> {
    let mut first: Vec<char> = Vec::new();
    let put = |row: &mut Vec<char>, col: usize, s: &str| {
        for (k, ch) in s.chars().enumerate() {
            if row.len() <= col + k {
                row.resize(col + k + 1, ' ');
            }
            row[col + k] = ch;
        }
    };
    for (col, len, label) in marks {
        let ch = if label.primary { "^" } else { "-" };
        put(&mut first, *col, &ch.repeat(*len));
    }
    let mut stacked = Vec::new();
    for (i, (col, len, label)) in marks.iter().enumerate() {
        if label.text.is_empty() {
            continue;
        }
        let text_col = col + len + 1;
        let fits = match marks.get(i + 1) {
            None => true,
            Some((next, _, _)) => text_col + label.text.chars().count() < *next,
        };
        if fits {
            put(&mut first, text_col, &label.text);
        } else {
            stacked.push((*col, label.text.as_str()));
        }
    }
    let mut rows = vec![first.into_iter().collect::<String>()];
    if stacked.is_empty() {
        return rows;
    }
    // One row of connectors, then the stacked texts from right to left.
    let mut connectors = Vec::new();
    for (col, _) in &stacked {
        put(&mut connectors, *col, "|");
    }
    rows.push(connectors.into_iter().collect());
    for k in (0..stacked.len()).rev() {
        let mut row = Vec::new();
        for (col, _) in &stacked[..k] {
            put(&mut row, *col, "|");
        }
        put(&mut row, stacked[k].0, stacked[k].1);
        rows.push(row.into_iter().collect());
    }
    rows
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_like_rustc() {
        let src = "fn dup(s: String) -> (String, String) {\n    (s, s)\n}\n";
        let d = Diagnostic::new("E0382", "use of moved value: `s`")
            .with(Label::secondary(
                Span::new(7, 8),
                "move occurs because `s` has type `String`, which does not implement the `Copy` trait",
            ))
            .with(Label::secondary(Span::new(45, 46), "value moved here"))
            .with(Label::primary(Span::new(48, 49), "value used here after move"));
        let expected = "\
error[E0382]: use of moved value: `s`
 --> dup.aff:2:9
  |
1 | fn dup(s: String) -> (String, String) {
  |        - move occurs because `s` has type `String`, which does not implement the `Copy` trait
2 |     (s, s)
  |      -  ^ value used here after move
  |      |
  |      value moved here
";
        assert_eq!(d.render("dup.aff", src), expected);
    }
}
