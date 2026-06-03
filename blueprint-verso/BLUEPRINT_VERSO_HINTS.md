# Building the blueprint

lake exe blueprint-gen --output _out/site

Run this in directory blueprint-verso

# Looking at the blueprint

cd blueprint-verso/_out/site/html-multi && python3 -m http.server 8000

Then open http://localhost:8000/ in a browser. Ctrl+C in the terminal stops it.
