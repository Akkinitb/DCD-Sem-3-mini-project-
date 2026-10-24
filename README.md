# ⚡ Boolean Expression Simplifier

A dashboard-style web app that simplifies Boolean expressions, built with Python and Streamlit for a Digital Circuit Design (DCD) assignment.

**Live app:** _add your Streamlit link here_

## Features

- Personalised output: enter your name and results are addressed to you
- Flexible input: `AB + A'C + BC`, `(A+B)(A'+C)`, `A xor B`, `!A & (B|C)`
- Minimal **SOP** and **POS** forms using Quine–McCluskey (via SymPy)
- Canonical Σm / ΠM lists and automatic equivalence check
- Truth table, Karnaugh map (2–4 variables)
- Step-by-step Quine–McCluskey working with prime implicants
- Gate-level circuit diagrams, original vs simplified, with gate and literal savings
- History of past inputs and a downloadable text report

## Input syntax

| Operation | Accepted |
|---|---|
| AND | `AB`, `A.B`, `A*B`, `A&B`, `A and B` |
| OR | `A+B`, `A\|B`, `A or B` |
| NOT | `A'`, `!A`, `~A`, `not A`, `(A+B)'` |
| XOR | `A^B`, `A⊕B`, `A xor B` |
| Constants | `0`, `1` |

Each letter is a separate variable (case-insensitive), so `ABC` means A·B·C. Precedence: NOT › AND › XOR › OR. Up to 8 variables.

## Run locally

```bash
git clone <your-repo-url>
cd boolean-simplifier
pip install -r requirements.txt
streamlit run app.py
```

## Deploy on Streamlit Community Cloud

1. Push this repo to GitHub.
2. Go to [share.streamlit.io](https://share.streamlit.io) and click **New app**.
3. Select the repo and branch, set the main file to `app.py`, and click **Deploy**.

## Example

Input: `AB + A'C + BC`

- Minimal SOP: `F = AB + A'C`
- Minimal POS: `F = (A' + B)(A + C)`

The `BC` term is redundant by the consensus theorem.

## Project structure

```
app.py               # Streamlit app: parser, minimiser, K-map, Q-M, circuit
requirements.txt     # Dependencies
.streamlit/config.toml  # Dark theme
```

## Tech stack

Python · Streamlit · SymPy · pandas · Graphviz (rendered by Streamlit)

## License

MIT, see [LICENSE](LICENSE).
