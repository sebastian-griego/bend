Review regression fixtures
==========================

The 14 fixtures cover the two examples in issue #1623, their controls,
and every scenario listed in the review of PR #1657. They do not change
the exporter or either kernel.

Source checks
-------------

Bun 1.3.14 accepted all 12 positive fixtures and rejected both negative
fixtures on both source versions:

- Pinned source: 234cb9b950800f20b15feafcb4ce2f43e76e7fae.
- Current source: 4982c105b9e8e06cc1d1e2d0d63c546dac4aa377.

The exact generic example from the issue still parses on both versions.
No syntax or quantity change was necessary. The ctr_param_field_eta file
is an exact copy from the current source version. It also parses on the
pinned version. Its implicit and explicit quantity arguments are retained.

The source results alone do not establish kernel acceptance. The common
runner tests the exported books against the available kernels. The
manifest's desired_candidate value states the intended result. It is not
a recorded test result.

Meanings and provenance
-----------------------

issue1623_reuse is the exact program in the issue body. It proves
reflexivity after a match rebuilds the value passed to the helper.
issue1623_direct proves the same branch goal without the helper.
issue1623_original passes the original value to the same helper.

issue1623_generic is the exact program in viridale's comment. A generic
rebuild and a rebuild specialized to Nat -> Nat both return their input.
The theorem equates their results in each constructor case.
issue1623_nat_control replaces every occurrence of (Nat -> Nat) with Nat.
This is the control requested in that comment.

review_field_argument_helper constructs the same Box in a helper result
and in the caller's expected type. review_unfold_box and
review_unfold_maybe unfold a constructor builder. review_rewrite_field
uses an explicit equality hypothesis to replace a field value.
review_eta_equal_fields compares f with its eta expansion inside Box.
review_named_id compares a stored definition with its eta expansion.
These are minimal implementations of the scenarios in the PR review.

review_ctr_param_field_eta is the existing repository regression named
in that review. It covers the pair and Maybe parameterized field cases.

negative_unrelated_field asserts equality of Box{f} and Box{g} for
arbitrary f and g without an equality hypothesis.
negative_unrelated_helper tries to prove that claim with reflexivity at
Box{f}. Both claims must be rejected. The normal source pipeline rejects
them before it invokes a kernel. They are source controls, not independent
negative tests of kernel conversion. The reference's direct kernel tests
supply that separate coverage.

References
----------

https://github.com/bendlang/bend/issues/1623
https://github.com/bendlang/bend/issues/1623#issuecomment-6305183385
https://github.com/bendlang/bend/pull/1657
https://github.com/bendlang/bend/blob/4982c105b9e8e06cc1d1e2d0d63c546dac4aa377/tests/check/ctr_param_field_eta.bend
