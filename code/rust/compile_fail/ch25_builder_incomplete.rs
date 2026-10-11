// harness: compile-fail E0599
//! A missing required field is a type error: `build` exists only on
//! `RequestBuilder<Method, Url>`.

pub struct NoMethod;
pub struct NoUrl;
pub struct Method(pub &'static str);
pub struct Url(pub String);

pub struct RequestBuilder<M, U> {
    method: M,
    url: U,
}

impl RequestBuilder<NoMethod, NoUrl> {
    pub fn new() -> Self {
        RequestBuilder {
            method: NoMethod,
            url: NoUrl,
        }
    }
}

impl<U> RequestBuilder<NoMethod, U> {
    pub fn method(self, m: &'static str) -> RequestBuilder<Method, U> {
        RequestBuilder {
            method: Method(m),
            url: self.url,
        }
    }
}

impl RequestBuilder<Method, Url> {
    pub fn build(self) -> (String, String) {
        (self.method.0.to_string(), self.url.0)
    }
}

// ANCHOR: incomplete
pub fn request() -> (String, String) {
    RequestBuilder::new().method("GET").build()
}
// ANCHOR_END: incomplete
