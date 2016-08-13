# RM Zoo

The Reverse Mathematics Zoo is a program to help organize relations among various mathematical principles, particularly those that fail to be equivalent to any of the big five subsystems of second-order arithmetic. Its primary goal is to make it easier to see known results and open questions, and thus hopefully to serve as a useful tool to researchers in the field. As a secondary goal, the Zoo should provide an interactive annotated bibliography of the field, collecting results in a standard machine-readable format.

The present version of the RM Zoo is a complete rewrite of the original, and features many improvements. The program has been heavily optimized and extended; the run time should generally be faster, and more true facts should be inferred from most starting results files. In addition, the RM Zoo can now handle implications, reducibilities (including both Weihrauch reducibility and computable reducibility), and conservation facts.

The program is divided into two parts: a database updater/compiler, which derives all inferences from the provided results file, and a database query system, which can answer specific questions about reverse-mathematical relations or produce diagrams on request.

Under the reverse-mathematical interface, the Zoo is actually a specialized inference engine, designed to reason with facts of the form "a implies b in context Q" (implication facts), "if a implies p, and p has form F, then b implies p" (conservation facts), or the negations thereof.

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

### rmupdater

`rmupdater.py` compiles results files into databases of known facts, and is typically run as follows:

- `python rmupdater.py [results file]`,

where `[results file]` is a text file containing facts; the results file included in this distribution is `byPaper.txt`. If using multiple results files (for testing purposes), you may keep them in separate databases by adding a database title:

- `python rmupdater.py [results file] [database title]`

For example, one would typically run

- `python rmupdater.py byPaper.txt`;

If maintaining an alternate results file in `test.txt`, one might separately run the command

- `python rmupdater.py test.txt testDatabase`.

### rmzoo

`rmzoo.py` then takes the database built by `rmupdater.py`, and carries out various tasks as controlled by its options. The basic command is

- `python rmzoo.py [options]`;

however, if you need to specify a database title, add it to the command as follows:

- `python rmzoo.py [database title] [options]`

---

To query the database for a fact (which will determine whether it is known or contradicted, and give the justification in either case), run the command

- `python rmzoo.py -q "[fact]"`.

For example,

- `python rmzoo.py -q "RT22 -> CRT22"`

will print a justification of the fact that **RT<sup>2</sup><sub>2</sub>** implies **CRT<sup>2</sup><sub>2</sub>** over **RCA<sub>0</sub>**.

---

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
- `-r "[CLASS]"`: restrict the diagram to just the principles contained between the quotation marks (and any sub-principles of conjunctions in the list). For example, the option `-r "RT22 COH+WKL SRT22 RCA"` will show only relations between the principles **RT22**, **COH+WKL**, **SRT22**, **RCA<sub>0</sub>**, **COH**, and **WKL**.

For instance,

- `python rmzoo.py -i -o -w > diagram.dot`

will produce a diagram of all implications between principles that hold in ω-models, along with the weakest open implications (in ω-models). Generally speaking, the more options that are selected, the more information is shown on the diagram; this tends to make it harder to read.

It would probably be of very limited use to select *all* the options, for instance.

## Credits

The RM Zoo was originally developed by Damir Dzhafarov, inspired by Joseph S. Miller's command-line version of the Computability Menagerie. Recently, the Zoo has been largely rewritten by Eric Astor to improve performance, expand the library of available inference rules, and move to a more maintainable/upgradeable architecture.

Many people have helped with the RM Zoo, by commenting on the code, contributing facts, suggesting new features, or just expressing their interest. Thanks in particular to David Belanger, Peter Cholak, Stephen Flood, Denis Hirschfeldt, Steffen Lempp, Joe Miller, Antonio Montalbán, Carl Mummert, Ludovic Patey, Sam Sanders, and Ted Slaman.

## Contributing

Contributions and/or feedback are, of course, welcome! If you are comfortable working with GitHub, the best way to contribute is as follows:

1. Fork the code.
2. Create your feature branch: `git checkout -b my-new-feature`
3. Commit your changes: `git commit -am 'Add some feature'`
4. Push to the branch: `git push origin my-new-feature`
5. Submit a pull request.

Otherwise, don't hesitate to send an e-mail or other message.

### Results

The results file is a simple text file containing relations between reverse-mathematical principles. This is then compiled by the Zoo's updater to create its database, which is then used by the Zoo to generate its various outputs (whether DOT files or text responses).

#### Names

Principles should be named by **simple plaintext alphanumeric strings** that resemble their normal acronyms in the literature; for example, we use `RT22` for Ramsey's theorem for pairs (and 2 colors). Do not use TeX in the names of principles (as in `RT^2_2` or `\mathsf{RT}^2_2`); this will make the diagrams harder to read, as DOT files have no TeX support, and can sometimes cause errors.

#### Relations

Relations between principles are given by using various operators. For instance:

- `RT22 -> COH`

indicates an **implication** provable in **RCA<sub>0</sub>**. By itself, however, this would generate an error; all facts must include a **justification**. To justify this fact, one would instead write:

- `RT22 -> COH "Mileti (2004) [Claim A.1.3], and independently Jockusch and Lempp"`

These justifications are used by the Zoo to keep track of why the facts it derives are true, and as such are important for maintaining a usable database. For simplicity, justifications should also be plaintext; if a principle needs to be mentioned, the same acronyms as for relations should be used. To keep the results file clean, please use the justification format: "Author 1, Author 2, and Author 3 (year) \[result citation\]". If possible, citations should be to the authoritative published version of the paper, falling back to an arXiv citation only when the authoritative version is not yet available.

**Non-implications** (i.e., implications known *not* to be provable in **RCA<sub>0</sub>**), can be entered similarly, using the operator `-|>`; for example,

- `RT22+WKL -|> ACA "Seetapun and Slaman (1995) [Theorem 3.1]"`

However, this result said more than this; Seetapun and Slaman specifically constructed an omega-model of **RT22+WKL** in which **ACA** failed. In general, one can represent implications and non-implications over omega-models by prepending `w` before an operator. Thus, one can more accurately write the previous result as

- `RT22+WKL w-|> ACA "Seetapun and Slaman (1995) [Theorem 3.1]"`

and might also write

- `COH w-> StCOH "Hirschfeldt and Shore (2007) [Proposition 4.4]"`

to represent this implication which, while not necessarily true in all models of **RCA<sub>0</sub>**, holds over all omega models. The Zoo is programmed to understand that `->` is stronger than `w->`, and thus that `w-|>` is stronger than `-|>`.

Furthermore, the Zoo now supports results from the study of computable and Weihrauch reducibilities, using the operators `<=` and `</=`, and appending an abbreviation of the relevant reducibility. For example, the following facts could be included in the results file:

- `DNR <=_c SRT22 "Hirschfeldt, Jockusch, Kjos-Hanssen, Lempp, and Slaman (2008) [follows from proof of Theorem 2.3]"`
- `COH </=_W SRT22 "Dzhafarov (to appear) [Corollary 4.5]"`

The supported reducibilities are:

- strong Weihrauch reducibility (`sW`)
- Weihrauch/uniform reducibility (`W`)
- generalized Weihrauch reducibility (`gW`)
- strong computable reducibility (`sc`)
- computable reducibility (`c`)
- generalized computable reducibility (`gc`) \[also known as reducibility over omega-models (`w`)\]

The Zoo understands the relations between these reducibilities, and between them and the above notions of implication. Thus, it can conclude from the above examples that `SRT22 w-> DNR` and that `COH </=_sW SRT22`.

##### Equivalences and Primary Principles

The Zoo can handle cycles without difficulty. For example, it will know that the facts

- `StCOH -> StCADS`
- `StCADS -> StCOH`

together indicate that the principles **StCOH** and **StCADS** are **equivalent** over **RCA<sub>0</sub>**, and will act accordingly. For instance, if rendering a diagram, the Zoo will pick one of the two principles to treat as 'primary', in the sense that implications and non-implications will only be shown going to and from the primary principle; this reduces the mess, and keeps the diagram more readable. Of course, the Zoo may occasionally pick the "wrong" primary principle; for instance, we probably want **StCOH** to be considered primary over **StCADS**. Since the Zoo has no way of knowing that on its own, we can include the fact

- `StCOH is primary`

in our results file, and ensure that the Zoo considers **StCOH** to be the primary principle. (Note that our choice of primary principles is given no justification; in fact, by the standards of the results file, it *cannot* be justified.) The order in which this is done matters. For example, if we switch to thinking about omega models, **StCOH** will be equivalent to **COH**, but we probably want **COH** to be considered primary in this case. Entering

- `COH is primary`

**earlier** (i.e., "higher up") in the results file will achieve the desired result.

Principles can also be declared equivalent by use of dedicated operators, included for convenience. Writing

- `StCOH <-> StCADS`

will produce the same result as including both of the two separate implications. (**Warning:** prepending a `w` to `<->` does work, but does not merely indicate an equivalence that holds over omega models; it in fact asserts that both halves of the implication hold in omega models. One can use the operator `<=>` in a similar way, subject to the same caveat.)

#### Syntactic Forms and Conservation Facts

The Zoo also understands **syntactic forms** and **conservations facts** relating reverse-mathematical principles. Specifically, it understands the syntactic forms 

- `Sig02`, `Pi02`, `Sig03`, `Pi03`, `Sig04`, and `Pi04`: three levels of the arithmetic hierarchy
- `Pi11`, `Pi12`, and `Pi13`: the first three universal levels of the analytic hierarchy
- `uPi03`: Pi03 with a single universally-quantified set paramater; defined as "twiddle-Pi<sup>0</sup><sub>3</sub>" in Patey and Yokoyama (preprint)
- `rPi12`: restricted Pi12 statements, as defined in Hirschfeldt and Shore (2007) \[Corollary 2.21\]

We can thus enter

- `RT22 form rPi12`
- `BSig2 form Pi11`

to indicate that the given principles have the given forms. (Note that these statements are **unjustified**.)

To indicate that one principle is conservative over another for consequences of a given form (that is to say, the first proves no more consequences of that form than the second), we can add results such as:

- `AMT+BSig2 Pi11c BSig2 "Hirschfeldt, Shore, and Slaman (2009) [Corollary 4.5]"`
- `AMT rPi12c RCA "Hirschfeldt, Shore, and Slaman (2009) [Corollary 3.15]"`

To indicate that one principle is **not** conservative over another, prepend an `n` before the conservation operator. For instance, we might add the result

- `RT22 nPi04c RCA "Seetapun and Slaman (1995) [Theorem 3.6]"`

Conservation and non-conservation facts must, again, be justified. The Zoo understands the connections between conservation facts and implications, and will use them to extract more relations between the known principles.

#### Compound Principles (i.e., Conjunctions)

As the reader may have noted above, the Zoo also understands compound principles; that is, principles that are conjunctions of other principles. For instance, if we add

- `SRT22+COH <-> RT22`

as a fact in the results file, the Zoo will know that `COH+SRT22` is a compound principle, denoting the conjunction of `COH` and `SRT22`. It will add any component principles to its internal list, and automatically understands the relations between the compound principle and its components. 

#### Organization and Formatting

Please note that any line in the results file starting with a `#` symbol is ignored, and considered to be a comment for human readers.

If contributing to the results file, please take note of the organization formatting used therein; we have organized the results by publication, arranged by publication year when possible (with the noted exception of Simpson's "Subsystems of Second-Order Arithmetic" \[also known as SOSOA\], which is listed first). Each publication's results should be preceded by a comment containing a full authoritative citation, including (if at all possible) a URL and DOI for the authoritative published version.

Contributions to the results file are extremely welcome. For example, if anyone wants to transcribe the relevant results of Simpson's SOSOA into our format, the maintainers would be eternally grateful! (For context, please note that this textbook is over 450 pages long.)

## License

The RM Zoo has been placed under the MIT license; in plain English, you can do whatever you want with it, including redistribution and creation of derivative works, as long as attribution and the appropriate license information remain. For details, please see the LICENSE file.
