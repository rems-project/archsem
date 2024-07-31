Require Import ZArith.
Require Import Options.
Require Import CBase.

Require Import Extraction.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatBigInt.

Extraction Blacklist String.
Extract Inlined Constant ctrans => "(fun x -> x)".
Extraction Implicit ctrans [CTrans x y].
