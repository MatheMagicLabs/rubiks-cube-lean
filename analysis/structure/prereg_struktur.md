# Pre-registration: structure exploration (10 Oct 2026, 01:40 UTC)
Already done BEFORE this registration (exploratory, NOT pre-registered):
- exact element-order distribution (theorem-type computation, checked by |G| and Frobenius);
- shortest word of order exactly 11 = 10 moves (17,760 canonical words) -- found before registering.

Hypotheses registered now (to be tested after this hash is recorded):
H1 (order-11 distances): for 100 uniformly random elements of order 11, optimal HTM distance:
    mean in [16.5, 18.0]; maximum <= 19; minimum >= 13.
H2 (order-11 vs random): the mean distance of order-11 elements is within 0.5 of the mean of
    100 uniformly random cube positions solved the same way (expected ~17.7).
H3 (Bad18 structure): the 1352 distance-18 elements of H=<U,D,R2,L2,F2,B2> fall into <= 60 orbits
    under the 16 U-D symmetries together with inversion; at least 90% of them have a fixed corner
    permutation parity class (all are even overall anyway); prediction: none of them has corners solved.
H4 (476 hardest phase-1 cells): all 476 cells have the E-slice edges entirely outside the E-slice?
    Prediction: at least 50% of the 476 have all 4 E-slice edges outside the E slice.
H5 (insertion / coset argument): for the 476 hardest cells, the minimum over all length-12 phase-1
    solutions of the phase-2 distance is <= 16 for every position (this is exactly what the formal
    28-proof certifies; prediction: true, already known from the C feasibility run - listed only for completeness).
H6 (slice groups): God's number of <RL', UD', FB'> (order 768 expected) in the face-pair metric is <= 8;
    God's number of <RL, UD, FB> (order 6144 expected) <= 12.
