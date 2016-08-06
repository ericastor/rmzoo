# RM Zoo

The Reverse Mathematics Zoo is a program to help organize relations among various mathematical principles, particularly those that fail to be equivalent to any of the big five subsystems of second-order arithmetic. Its primary goal is to make it easier to see known results and open questions, and thus hopefully to serve as a useful tool to researchers in the field. As a secondary goal, the Zoo should provide an interactive annotated bibliography of the field, collecting results in a standard machine-readable format.

The present version of the RM Zoo is a complete rewrite of the original, and features many improvements. The program has been heavily optimized and extended; the run time should generally be faster, and more true facts should be inferred from most starting results files. In addition, the RM Zoo can now handle implications, reducibilities (including both Weihrauch reducibility and computable reducibility), and conservation facts.

The program is divided into two parts: a database updater/compiler, which derives all inferences from the provided results file, and a database query system, which can answer specific questions about reverse-mathematical relations or produce diagrams on request.

## Installation

To run the RM Zoo, you will need to install a distribution of Python, version 2.7 or later. (The Zoo will perform best if run in either [PyPy2.7](http://pypy.org/index.html) or [Python 3.4+](https://www.python.org/).)

You will also need the [Pyparsing](http://pyparsing.wikispaces.com/) module.

If not using Python 3.4+, you will need to install the [enum34](https://bitbucket.org/stoneleaf/enum34) module, and if not using Python 3.2+, you will also need the [repoze.lru](https://github.com/repoze/repoze.lru) module.

To install each of these modules, run the appropriate commands below:
```
pip install pyparsing
pip install enum34
pip install repoze.lru
```

To view/render the diagrams produced by the Zoo, you will need to install [Graphviz](http://www.graphviz.org/), or another program capable of reading DOT files.

## Usage

The RM Zoo consists of two Python scripts, `rmupdater.py` and `rmzoo.py`.

`rmupdater.py` compiles results files into databases of known facts, and is typically run as follows:

- `python rmupdater.py [results file]`,

where `[results file]` is a text file containing facts; the results file included in this distribution is `byPaper.txt`. If using multiple results files (for testing purposes), you may keep them in separate databases by adding a database title:

- `python rmupdater.py [results file] [database title]`

For example, one would typically run

- `python rmupdater.py byPaper.txt`;

If maintaining an alternate results file in `test.txt`, one might separately run the command

- `python rmupdater.py test.txt testDatabase`.



`rmzoo.py` then takes the database built by `rmupdater.py`, and carries out various tasks.

To query the database for a fact (which will determine whether it is known or contradicted, and give the justification in either case), run the command

- `python rmzoo.py -q "[fact]"`.

For example,

- `python rmzoo.py -q "RT22 -> CRT22"`

will print a justification of the fact that `RT22` implies `CRT22` over `RCA`<sub>0</sub>.

To generate a diagram from the database, instead run

- `python rmzoo.py [diagram options] > [destination]`,

where `[destination]` is a DOT file. The `[diagram options]` **must** include one or more of the following:

- `-i`: show implications as black arrows;
- `-n`: show non-implications as red arrows;
- `-f`: color-codes principles by their syntactic form; currently, this uses a pink box for Π<sup>1</sup><sub>1</sub> principles, and a cyan box for restricted Π<sup>1</sup><sub>2</sub> principles. Other forms do not yet have a color code.
- `-c`: show conservation facts, using color-coded arrows (as for the forms) to represent each form of conservation;
- `-w`: show the weakest open implications as green arrows;
- `-s`: show the strongest open implications as green arrows.
In addition, the options may include any of the following:
- `-o`: show facts that hold in ω-models;
- `-t [REDUCIBILITY]`: show facts relative to implications over the given REDUCIBILITY (options include sW, W, gW, sc, c, w, and RCA);
- `-p`: show only one primary principle from each group of equivalent principles;
- `-r "[CLASS]"`: restrict the diagram to just the principles contained between the quotation marks (and any sub-principles of conjunctions in the list). For example, the option `-r "RT22 COH+WKL SRT22 RCA"` will show only relations between the principles `RT22`, `COH+WKL`, `SRT22`, `RCA`, `COH`, and `WKL`.

For instance,

- `python rmzoo.py -i -o -w > diagram.dot`

will produce a diagram of all implications between principles that hold in ω-models, along with the weakest open implications (in ω-models). Generally speaking, the more options that are selected, the more information is shown on the diagram; this tends to make it harder to read.

It would probably be of very limited use to select *all* the options, for instance.

## Contributing

1. Fork it!
2. Create your feature branch: `git checkout -b my-new-feature`
3. Commit your changes: `git commit -am 'Add some feature'`
4. Push to the branch: `git push origin my-new-feature`
5. Submit a pull request.

If contributing to the results file, please try to stick to the format used therein, including detailed citations for each result and (if possible) an authoritative URL for the published version of the referenced paper.

## Credits

The RM Zoo was originally developed by Damir Dzhafarov, inspired by Joseph S. Miller's command-line version of the Computability Menagerie. The corresponding results file received various contributions, in particular by Damir and by Ludovic Patey.

Recently, the Zoo has been largely rewritten by Eric Astor to improve performance, expand the library of available inference rules, and move to a more maintainable/upgradeable architecture.

## License

The RM Zoo has been placed under the MIT license; in plain English, you can do whatever you want with it, including redistribution and creation of derivative works, as long as attribution and the appropriate license information remain. For details, please see the LICENSE file.
