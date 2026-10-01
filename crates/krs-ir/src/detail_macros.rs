macro_rules! details {
    ($(#[$doc:meta])* $name:ident { $($variant:ident => $text:literal,)* }) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
        pub enum $name {
            $(#[doc = concat!("`", $text, "`.")] $variant,)*
        }

        impl ::std::fmt::Display for $name {
            fn fmt(&self, formatter: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                formatter.write_str(match self {
                    $(Self::$variant => $text,)*
                })
            }
        }
    };
}

pub(crate) use details;
