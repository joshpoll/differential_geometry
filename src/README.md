# GOAL
Formalize smooth manifolds. My approach is inspired by and builds directly off of Patrick Massot's work. I anticipate we will coalesce in the future.

What's required?

1. Continuity Proofs
2. Differentiability Proofs
3. Definition of Smooth
4. Topological Manifolds
5. Smooth Manifolds
6. Examples and Theorems

The approach for differentiability will be to use the Caratheodory derivative. Since this deviates from the conventional Frechet derivative, its use must be justified.

1. **Key:** Caratheodory proofs do not require epsilon-delta arguments. Limits are hidden behind continuity.
2. Caratheodory iff Frechet for Banach Spaces
3. Caratheodory generalizes more readily to more abstract spaces
4. Caratheodory has been used by other formalizations.
5. The operator norm must be defined up front (this point is not very convincing. May also be needed for Frechet)

What is the right way to formalize these structures?
Structures? Classes? Combinations of predicates?
Different parts of mathlib take different approaches. I'm not sure if this is by necessity or b/c no one's figured out which one is right yet.
