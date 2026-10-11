// harness: compile-fail E0283
//! A trait with a type parameter is a relation: `Celsius` converts to two
//! targets, and nothing says which one is meant.

struct Celsius(f64);
struct Fahrenheit(f64);
struct Kelvin(f64);

trait ConvertTo<Target> {
    fn convert(&self) -> Target;
}

impl ConvertTo<Fahrenheit> for Celsius {
    fn convert(&self) -> Fahrenheit {
        Fahrenheit(self.0 * 9.0 / 5.0 + 32.0)
    }
}

impl ConvertTo<Kelvin> for Celsius {
    fn convert(&self) -> Kelvin {
        Kelvin(self.0 + 273.15)
    }
}

// ANCHOR: ambiguous
fn show(c: &Celsius) {
    let t = c.convert();
}
// ANCHOR_END: ambiguous
