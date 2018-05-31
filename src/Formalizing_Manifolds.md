- Type Theory (vs. Set Theory)
- Propositions as Types. Proofs as Terms
  - We can compose proofs just like functions.
  - lambda, Pi, forall
  - pair, Sigma, exists (notice tangent bundle is a dependent product)
- Constructive by default
- HoTT vs Martin Lof. Tradeoff b/c multiple parties involved.
- B/c of curry-howard-lambek, can apply software engineering practices to mathematics
  - separation of concerns and DRY
  - even though isomorphic...
    - continuous linear maps > bounded linear maps
    - caratheodory derivative > frechet derivative
  - charts before manifolds
  - order-theory-influenced definitions for topology (still don't fully understand this choice)
- How to formalize
  1. determine if structure with new properties or subset of existing structure
    - New Properties
      1. Define structure.
      2. ?
    - Subset
      1. Create proposition that defines the subset
      2. Prove composition lemmas about the proposition
      3. Create subtype based on proposition
      4. Create composition functions for the subtype and wrap them up in spaces.


Questions to think about
- Is a topological manifold as subtype of topological space or a topological space with additional structure? Couldn't it be encoded both ways? Maybe want to make a function that produces coordinate neigbhorhoods, prove things about that and then define topological space.