// harness: run
//! The rest of the type-class toolbox, in Rust: associated types versus type
//! parameters, supertraits, default methods and blanket impls, and what a
//! supertrait and a default method become after the dictionary-passing
//! translation.
//!
//! Run with: `cargo run --example ch14_trait_features`

use std::fmt::{self, Debug, Display};

// ANCHOR: units
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
struct Celsius(f64);

#[derive(Clone, Copy, Debug, PartialEq)]
struct Fahrenheit(f64);

#[derive(Clone, Copy, Debug, PartialEq)]
struct Kelvin(f64);

impl Display for Celsius {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:.1} °C", self.0)
    }
}
// ANCHOR_END: units

// ANCHOR: type_parameter
/// A trait with a type parameter: a *relation* between two types. One type
/// may implement it many times, once for each target.
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
// ANCHOR_END: type_parameter

// ANCHOR: supertrait
/// Every instrument has a name.
trait Device {
    fn name(&self) -> String;
}

/// A sensor is a device that produces readings. `Device` is a supertrait:
/// a type can implement `Sensor` only if it also implements `Device`.
trait Sensor: Device {
    /// An associated type: a *function* from sensor types to reading types.
    type Reading: Debug;

    fn read(&mut self) -> Self::Reading;

    /// A default method, written once in terms of the other methods (including
    /// the supertrait's `name`). Instances may use it or override it.
    fn report(&mut self) -> String {
        let reading = self.read();
        format!("{}: {reading:?}", self.name())
    }
}
// ANCHOR_END: supertrait

// ANCHOR: sensor_instances
/// Replays recorded temperatures.
struct Thermometer {
    label: String,
    recorded: Vec<Celsius>,
    next: usize,
}

impl Device for Thermometer {
    fn name(&self) -> String {
        self.label.clone()
    }
}

impl Sensor for Thermometer {
    type Reading = Celsius;
    fn read(&mut self) -> Celsius {
        let reading = self.recorded[self.next % self.recorded.len()];
        self.next += 1;
        reading
    }
    // `report` is not written here: the default is used.
}

/// A door switch that reads `true` when the door is open.
struct DoorSwitch {
    open: bool,
}

impl Device for DoorSwitch {
    fn name(&self) -> String {
        "lab door".to_string()
    }
}

impl Sensor for DoorSwitch {
    type Reading = bool;
    fn read(&mut self) -> bool {
        self.open
    }
    // This instance overrides the default method.
    fn report(&mut self) -> String {
        let state = if self.read() { "open" } else { "closed" };
        format!("{} is {state}", self.name())
    }
}
// ANCHOR_END: sensor_instances

// ANCHOR: assoc_generic
/// Read `n` values. The return type mentions `S::Reading`, the value of the
/// type-level function `Reading` at `S`.
fn sample<S: Sensor>(sensor: &mut S, n: usize) -> Vec<S::Reading> {
    (0..n).map(|_| sensor.read()).collect()
}

/// A bound on the *result* of the type-level function: the readings must be
/// comparable (`PartialOrd`) and copyable.
fn peak<S>(sensor: &mut S, n: usize) -> Option<S::Reading>
where
    S: Sensor,
    S::Reading: PartialOrd + Copy,
{
    let readings = sample(sensor, n);
    let mut best = *readings.first()?;
    for &r in &readings {
        if r > best {
            best = r;
        }
    }
    Some(best)
}
// ANCHOR_END: assoc_generic

// ANCHOR: blanket
/// A blanket impl: *every* type that implements `Display` gets `Log`.
/// As an instance declaration: for all T, Display T implies Log T.
trait Log {
    fn log_line(&self) -> String;
}

impl<T: Display> Log for T {
    fn log_line(&self) -> String {
        format!("[log] {self}")
    }
}
// ANCHOR_END: blanket

// ANCHOR: dict_supertrait
/// The dictionary of `Device`.
struct DeviceDict<T> {
    name: fn(&T) -> String,
}

/// The dictionary of `Sensor`. The supertrait's dictionary is a field, the
/// associated type is a type parameter fixed by the instance, and the default
/// method is a field like any other.
struct SensorDict<T, R> {
    device: DeviceDict<T>,
    read: fn(&mut T) -> R,
    report: fn(&SensorDict<T, R>, &mut T) -> String,
}

/// The default method, translated: a function that receives the dictionary
/// it belongs to, so that it can call the other methods.
fn default_report<T, R: Debug>(dict: &SensorDict<T, R>, sensor: &mut T) -> String {
    let reading = (dict.read)(sensor);
    format!("{}: {reading:?}", (dict.device.name)(sensor))
}

/// `impl Sensor for Thermometer` uses the default `report`...
fn thermometer_dict() -> SensorDict<Thermometer, Celsius> {
    SensorDict {
        device: DeviceDict {
            name: <Thermometer as Device>::name,
        },
        read: <Thermometer as Sensor>::read,
        report: default_report,
    }
}

/// ...while `impl Sensor for DoorSwitch` overrides it. The override does not
/// need the dictionary, so this field wraps it in a closure that ignores it.
fn door_dict() -> SensorDict<DoorSwitch, bool> {
    SensorDict {
        device: DeviceDict {
            name: <DoorSwitch as Device>::name,
        },
        read: <DoorSwitch as Sensor>::read,
        report: |_dict, door| <DoorSwitch as Sensor>::report(door),
    }
}

/// A generic function with a `Sensor` bound, translated.
fn report_twice_dict<T, R>(dict: &SensorDict<T, R>, sensor: &mut T) -> [String; 2] {
    [(dict.report)(dict, sensor), (dict.report)(dict, sensor)]
}
// ANCHOR_END: dict_supertrait

/// The same function with a trait bound, for comparison.
fn report_twice<S: Sensor>(sensor: &mut S) -> [String; 2] {
    [sensor.report(), sensor.report()]
}

fn thermometer() -> Thermometer {
    Thermometer {
        label: "fridge".to_string(),
        recorded: vec![Celsius(4.5), Celsius(5.0), Celsius(3.5)],
        next: 0,
    }
}

fn main() {
    // ANCHOR: run_convert
    let c = Celsius(21.5);
    // With a type parameter, the caller must say which instance it means:
    // the *target* type selects the impl.
    let f: Fahrenheit = c.convert();
    let k: Kelvin = c.convert();
    println!("{c} = {f:?} = {k:?}");
    // ANCHOR_END: run_convert

    // ANCHOR: run_sensors
    let mut fridge = thermometer();
    let mut door = DoorSwitch { open: true };
    println!("sample:  {:?}", sample(&mut fridge, 4));
    println!("peak:    {:?}", peak(&mut fridge, 3));
    println!("default: {:?}", report_twice(&mut fridge));
    println!("custom:  {:?}", report_twice(&mut door));
    // ANCHOR_END: run_sensors

    // ANCHOR: run_dicts
    let (mut fridge_a, mut fridge_b) = (thermometer(), thermometer());
    let with_trait = report_twice(&mut fridge_a);
    let with_dict = report_twice_dict(&thermometer_dict(), &mut fridge_b);
    assert_eq!(with_trait, with_dict);
    let with_trait = report_twice(&mut DoorSwitch { open: false });
    let with_dict = report_twice_dict(&door_dict(), &mut DoorSwitch { open: false });
    assert_eq!(with_trait, with_dict);
    println!("dictionary versions agree: {with_dict:?}");
    // ANCHOR_END: run_dicts

    // ANCHOR: run_blanket
    // `Log` was never implemented for these types by name: the blanket impl
    // covers every `Display` type, from the standard library's or ours.
    println!("{}", 42.log_line());
    println!("{}", "door opened".log_line());
    println!("{}", Celsius(-18.0).log_line());
    // ANCHOR_END: run_blanket
}
