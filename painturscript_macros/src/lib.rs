// src/lib.rs
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, LitInt};

#[proc_macro]
pub fn declare_native_fn_aliases(input: TokenStream) -> TokenStream {
    let n = parse_macro_input!(input as LitInt);
    let arity = n.base10_parse::<usize>().unwrap();

    let arg_codes = ["N", "M", "V", "W"];
    let output_codes = ["N", "V", "FN", "FV"];

    let mut generated = quote! { };

    let arg_combinations = generate_combinations(&arg_codes, arity);

    for arg_combo in arg_combinations {
        for output_code in &output_codes {
            let alias_name = generate_alias_name(arity, &arg_combo, output_code);
            let (fn_type, need_lifetime) = generate_fn_type(arity, &arg_combo, output_code);

            let generic_params = generate_generic_params(&arg_combo, output_code);
            let alias = if need_lifetime {
                quote! {
                    pub type #alias_name<'a, #(#generic_params),*> = #fn_type;
                }
            } else {
                quote! {
                    pub type #alias_name<#(#generic_params),*> = #fn_type;
                }
            };

            generated.extend(alias);
        }
    }

    generated.into()
}

fn generate_combinations<'a>(codes: &'a [&'a str], arity: usize) -> Vec<Vec<&'a str>> {
    if arity == 0 {
        return vec![vec![]];
    }

    let mut result = vec![];
    let smaller_combinations = generate_combinations(codes, arity - 1);

    for combo in smaller_combinations {
        for &code in codes {
            let mut new_combo = combo.clone();
            new_combo.push(code);
            result.push(new_combo);
        }
    }
    result
}

fn fn_name(arity: usize) -> String {
    match arity {
        0 => "NullaryNativeFn".into(),
        1 => "UnaryNativeFn".into(),
        2 => "BinaryNativeFn".into(),
        3 => "TernaryNativeFn".into(),
        _ => format!("Fn{}Ary", arity),
    }
}

fn generate_alias_name(arity: usize, arg_codes: &[&str], output_code: &str) -> syn::Ident {
    let name = format!("{}{}{}", fn_name(arity), arg_codes.join(""), output_code);
    format_ident!("{}", name)
}

fn generate_fn_type(arity: usize, arg_codes: &[&str], output_code: &str) -> (syn::Type, bool) {
    let fn_type_name = format_ident!("{}", fn_name(arity));
    let mut need_lifetime = false;
    let arg_types = arg_codes
        .iter()
        .enumerate()
        .map(|(i, &code)| {
            let (ty, lifetime) = map_arg_code(code, i);
            need_lifetime |= lifetime;
            ty
        })
        .collect::<Vec<_>>();

    let output_type = map_output_code(output_code);

    (syn::parse_quote! {
        #fn_type_name<#(#arg_types,)* #output_type, F>
    }, need_lifetime)
}

fn map_arg_code(code: &str, index: usize) -> (syn::Type, bool) {
    let generic = format_ident!("A{}", index);
    match code {
        "N" => (syn::parse_quote! { NatVal<#generic> }, false),
        "M" => (syn::parse_quote! { NatMut<#generic> }, false),
        "V" => (syn::parse_quote! { Value }, false),
        "W" => (syn::parse_quote! { &'a mut Value }, true),
        _ => unreachable!(),
    }
}

fn map_output_code(code: &str) -> syn::Type {
    let output_generic = format_ident!("O");
    match code {
        "N" => syn::parse_quote! { NatVal<#output_generic> },
        "V" => syn::parse_quote! { Value },
        "FN" => syn::parse_quote! { Fallible<NatVal<#output_generic>> },
        "FV" => syn::parse_quote! { Fallible<Value> },
        _ => unreachable!(),
    }
}

fn generate_generic_params(arg_codes: &[&str], output_code: &str) -> Vec<syn::Ident> {
    let mut params = vec![];
    for (i, &code) in arg_codes.iter().enumerate() {
        if code == "N" || code == "M" {
            params.push(format_ident!("A{}", i));
        }
    }
    if output_code == "N" || output_code == "FN" {
        params.push(format_ident!("O"));
    }
    params.push(format_ident!("F"));
    params
}
