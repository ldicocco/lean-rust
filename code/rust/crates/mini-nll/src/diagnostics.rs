//! Error messages in the style of rustc: a header with the error code, the
//! source lines involved, and labels underlining parts of them (`^^^` for the
//! primary span, `---` for the others).

use std::collections::BTreeSet;

use crate::mir::{Body, Location, Span};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
    pub primary: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// `E0382`, `E0499`, ...
    pub code: &'static str,
    pub message: String,
    /// Where in the MIR the error was found.
    pub location: Location,
    pub labels: Vec<Label>,
}

impl Diagnostic {
    pub fn new(code: &'static str, message: String, location: Location) -> Diagnostic {
        Diagnostic {
            code,
            message,
            location,
            labels: Vec::new(),
        }
    }

    pub fn primary(&mut self, span: Option<Span>, message: impl Into<String>) {
        self.add(span, message.into(), true);
    }

    pub fn secondary(&mut self, span: Option<Span>, message: impl Into<String>) {
        self.add(span, message.into(), false);
    }

    fn add(&mut self, span: Option<Span>, message: String, primary: bool) {
        if let Some(span) = span {
            self.labels.push(Label {
                span,
                message,
                primary,
            });
        }
    }

    /// The first line of the message, `error[E0502]: cannot borrow ...`.
    pub fn headline(&self) -> String {
        format!("error[{}]: {}", self.code, self.message)
    }

    /// Render the diagnostic against the body's source text.
    pub fn render(&self, body: &Body) -> String {
        let lines: Vec<&str> = body.source.lines().collect();
        let mut labels = self.labels.clone();
        labels.sort_by_key(|l| (l.span.line, l.span.start));
        let annotated: BTreeSet<usize> = labels.iter().map(|l| l.span.line).collect();
        let width = annotated.iter().max().map_or(1, |l| l.to_string().len());
        let pad = " ".repeat(width);

        let mut out = format!("{}\n", self.headline());
        if let Some(p) = labels.iter().find(|l| l.primary) {
            let col = p.span.start + 1;
            out += &format!("{pad}--> {}:{}:{col}\n", body.file, p.span.line);
        }
        out += &format!("{pad} |\n");
        let mut previous: Option<usize> = None;
        for &line in &annotated {
            // Like rustc: show a single unannotated line between two annotated
            // ones, and `...` for a longer gap.
            if let Some(prev) = previous {
                if line == prev + 2 {
                    let text = lines[prev];
                    out += &format!("{:>width$} | {text}\n", prev + 1);
                } else if line > prev + 2 {
                    out += "...\n";
                }
            }
            out += &format!("{line:>width$} | {}\n", lines[line - 1]);
            let on_line: Vec<&Label> =
                labels.iter().filter(|l| l.span.line == line).collect();
            for text in annotate_line(&on_line) {
                out += &format!("{pad} | {}\n", text.trim_end());
            }
            previous = Some(line);
        }
        out
    }
}

/// The annotation lines under one source line, laid out as rustc does when
/// several labels share a line: all underlines first, the rightmost message
/// next to its underline, the others hanging below on vertical bars.
///
/// ```text
/// stack.push(stack.pop().unwrap());
/// ----- ---- ^^^^^ second mutable borrow occurs here
/// |     |
/// |     first borrow later used by call
/// first mutable borrow occurs here
/// ```
fn annotate_line(labels: &[&Label]) -> Vec<String> {
    let width = labels.iter().map(|l| l.span.end).max().unwrap_or(0);
    let mut marks = vec![' '; width];
    for label in labels {
        let mark = if label.primary { '^' } else { '-' };
        for c in &mut marks[label.span.start..label.span.end] {
            *c = mark;
        }
    }
    let last = labels.len() - 1;
    let mut out = vec![format!(
        "{} {}",
        marks.iter().collect::<String>(),
        labels[last].message
    )];
    // Vertical bars under the start of the first `k` labels.
    let bars = |k: usize| {
        let mut row = vec![' '; width];
        for label in &labels[..k] {
            row[label.span.start] = '|';
        }
        row.into_iter().collect::<String>()
    };
    if last > 0 {
        out.push(bars(last));
    }
    for k in (0..last).rev() {
        let mut row: String = bars(k).chars().take(labels[k].span.start).collect();
        row += &labels[k].message;
        out.push(row);
    }
    out
}
