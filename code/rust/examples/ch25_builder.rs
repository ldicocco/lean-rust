// harness: run
//! Builders with required fields. A builder that checks at run time (and
//! returns an error) next to a typestate builder whose `build` method exists
//! only once the method and the URL have both been set, in either order.
//!
//! Run with: `cargo run --example ch25_builder`

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Method {
    Get,
    Post,
}

/// The finished request: every required field is present.
#[derive(Debug)]
pub struct Request {
    method: Method,
    url: String,
    headers: Vec<(String, String)>,
    timeout_ms: u64,
}

impl fmt::Display for Request {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?} {} (timeout {} ms",
            self.method, self.url, self.timeout_ms
        )?;
        for (name, value) in &self.headers {
            write!(f, ", {name}: {value}")?;
        }
        write!(f, ")")
    }
}

// ANCHOR: dynamic
/// The usual builder: required fields are `Option`s, checked by `build`.
#[derive(Default)]
pub struct DynBuilder {
    method: Option<Method>,
    url: Option<String>,
    timeout_ms: Option<u64>,
}

#[derive(Debug)]
pub enum BuildError {
    MissingMethod,
    MissingUrl,
}

impl DynBuilder {
    pub fn method(mut self, method: Method) -> Self {
        self.method = Some(method);
        self
    }

    pub fn url(mut self, url: &str) -> Self {
        self.url = Some(url.to_string());
        self
    }

    pub fn build(self) -> Result<Request, BuildError> {
        Ok(Request {
            method: self.method.ok_or(BuildError::MissingMethod)?,
            url: self.url.ok_or(BuildError::MissingUrl)?,
            headers: Vec::new(),
            timeout_ms: self.timeout_ms.unwrap_or(30_000),
        })
    }
}
// ANCHOR_END: dynamic

// ANCHOR: typestate
/// Marker types: "not set yet". The set versions carry the value itself.
pub struct NoMethod;
pub struct NoUrl;
pub struct Url(String);

/// `M` is `NoMethod` or `Method`; `U` is `NoUrl` or `Url`. No `PhantomData`
/// is needed: the type parameters are the types of real fields.
pub struct RequestBuilder<M, U> {
    method: M,
    url: U,
    headers: Vec<(String, String)>,
    timeout_ms: u64,
}

impl RequestBuilder<NoMethod, NoUrl> {
    pub fn new() -> Self {
        RequestBuilder {
            method: NoMethod,
            url: NoUrl,
            headers: Vec::new(),
            timeout_ms: 30_000,
        }
    }
}

/// Setting the method: only possible while it is not set, whatever `U` is.
impl<U> RequestBuilder<NoMethod, U> {
    pub fn method(self, method: Method) -> RequestBuilder<Method, U> {
        RequestBuilder {
            method,
            url: self.url,
            headers: self.headers,
            timeout_ms: self.timeout_ms,
        }
    }
}

/// Setting the URL: only possible while it is not set, whatever `M` is.
impl<M> RequestBuilder<M, NoUrl> {
    pub fn url(self, url: &str) -> RequestBuilder<M, Url> {
        RequestBuilder {
            method: self.method,
            url: Url(url.to_string()),
            headers: self.headers,
            timeout_ms: self.timeout_ms,
        }
    }
}

/// Optional settings: available in every state, and they keep the state.
impl<M, U> RequestBuilder<M, U> {
    pub fn header(mut self, name: &str, value: &str) -> Self {
        self.headers.push((name.to_string(), value.to_string()));
        self
    }

    pub fn timeout_ms(mut self, ms: u64) -> Self {
        self.timeout_ms = ms;
        self
    }
}

/// `build` exists only when both required fields are set.
impl RequestBuilder<Method, Url> {
    pub fn build(self) -> Request {
        Request {
            method: self.method,
            url: self.url.0,
            headers: self.headers,
            timeout_ms: self.timeout_ms,
        }
    }
}
// ANCHOR_END: typestate

fn main() {
    // ANCHOR: dynamic_use
    let missing = DynBuilder::default().method(Method::Get).build();
    println!("dynamic, URL forgotten: {missing:?}");
    let ok = DynBuilder::default()
        .url("/samples")
        .method(Method::Get)
        .build();
    println!("dynamic, complete:      {}", ok.expect("both fields set"));
    // ANCHOR_END: dynamic_use

    // ANCHOR: typestate_use
    let a = RequestBuilder::new()
        .method(Method::Post)
        .header("content-type", "application/json")
        .url("/samples")
        .timeout_ms(500)
        .build();
    let b = RequestBuilder::new()
        .url("/samples/42")
        .method(Method::Get)
        .build();
    println!("typestate, method first: {a}");
    println!("typestate, URL first:    {b}");
    // ANCHOR_END: typestate_use

    println!(
        "size of RequestBuilder<NoMethod, NoUrl>: {} bytes",
        std::mem::size_of::<RequestBuilder<NoMethod, NoUrl>>()
    );
    println!(
        "size of RequestBuilder<Method, Url>:     {} bytes",
        std::mem::size_of::<RequestBuilder<Method, Url>>()
    );
}
