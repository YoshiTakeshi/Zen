# Simulations

Models that test the rules of Zen. Run them with `python3 file.py` or `node file.js` (JavaScript models write results into `js/results/`).

| File | What it tests |
|---|---|
| python/pom_simulation.py | Proof of Minting end to end with real signatures (about 1 to 2 minutes) |
| python/zen_minting.py | Collaborative block minting prototype and the anti-prime encoder |
| python/detect_sim.py, detect9.py | Detecting and attributing an attack with two versus three linked chains |
| js/model.js, model2.js, model3.js | Does 1 Jen = 1 Sen hold as more people agree; two coins one value; denominations and the ratio rule |
| js/twounit.js, wanchor.js, pegsize.js | Two units on one chain, the anchor on W, resizing blocks to steer W |
| js/daywin.js, receivers.js, bondsize.js, volsim.js, volsim2.js | Reading the Sen unit S: day windows, bonded receivers, volume counting, coin-days |
| js/pegdef.js, pegdef2.js | Defences against fake payments that try to move the peg |
| js/tri.js, tri2.js | Three chains, their exchange and the three-way brake |
| js/sim.js, q.js | Block resize rule, old versus balanced |
