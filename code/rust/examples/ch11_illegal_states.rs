// harness: run
//! Putting the algebra of types to work: two designs for the state of a
//! network link, their number of states, and an isomorphism between the legal
//! states of the first design and all the states of the second.
//!
//! Run with: `cargo run --example ch11_illegal_states`

// ANCHOR: designs
#[derive(Clone, Copy, Debug, PartialEq)]
enum Role {
    Reader,
    Writer,
    Admin,
}

/// Design 1: two independent fields, 2 × (1 + 3) = 8 states. The code that
/// uses it must trust an invariant: a link has a role exactly when it is
/// connected.
#[derive(Clone, Copy, Debug, PartialEq)]
struct LinkFlags {
    connected: bool,
    role: Option<Role>,
}

/// Design 2: one enum, 1 + 3 = 4 states, and no invariant to trust.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Link {
    Down,
    Up(Role),
}
// ANCHOR_END: designs

const ROLES: [Role; 3] = [Role::Reader, Role::Writer, Role::Admin];

// ANCHOR: conversions
impl LinkFlags {
    /// Every value of the type: |bool| × |Option<Role>| of them.
    fn all() -> Vec<LinkFlags> {
        let mut roles = vec![None];
        roles.extend(ROLES.map(Some));
        let mut out = Vec::new();
        for connected in [false, true] {
            for &role in &roles {
                out.push(LinkFlags { connected, role });
            }
        }
        out
    }

    fn is_legal(&self) -> bool {
        self.connected == self.role.is_some()
    }

    /// Partial: illegal combinations have no counterpart.
    fn to_link(self) -> Option<Link> {
        match (self.connected, self.role) {
            (false, None) => Some(Link::Down),
            (true, Some(role)) => Some(Link::Up(role)),
            (false, Some(_)) | (true, None) => None,
        }
    }
}

impl Link {
    /// Every value of the type: 1 + |Role| of them.
    fn all() -> Vec<Link> {
        let mut out = vec![Link::Down];
        out.extend(ROLES.map(Link::Up));
        out
    }

    /// Total: every `Link` is a legal `LinkFlags`.
    fn to_flags(self) -> LinkFlags {
        match self {
            Link::Down => LinkFlags {
                connected: false,
                role: None,
            },
            Link::Up(role) => LinkFlags {
                connected: true,
                role: Some(role),
            },
        }
    }
}
// ANCHOR_END: conversions

fn main() {
    // ANCHOR: run
    let flags = LinkFlags::all();
    for f in &flags {
        let verdict = match f.to_link() {
            Some(link) => format!("legal    -> {link:?}"),
            None => "ILLEGAL".to_string(),
        };
        println!(
            "connected: {:<5}  role: {:<12}  {verdict}",
            f.connected,
            format!("{:?}", f.role)
        );
    }
    let legal: Vec<LinkFlags> =
        flags.iter().copied().filter(LinkFlags::is_legal).collect();
    println!(
        "LinkFlags: {} states, {} legal, {} illegal",
        flags.len(),
        legal.len(),
        flags.len() - legal.len()
    );
    println!("Link:      {} states", Link::all().len());

    // The legal flags and the links are isomorphic: both round trips are the
    // identity, checked on every value.
    for link in Link::all() {
        assert_eq!(link.to_flags().to_link(), Some(link));
        assert!(link.to_flags().is_legal());
    }
    for f in legal {
        assert_eq!(f.to_link().map(Link::to_flags), Some(f));
    }
    println!("legal LinkFlags ≅ Link: both round trips checked");
    // ANCHOR_END: run
}
