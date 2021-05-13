## mLisa
## Lisp production-rule system (LISA) modified for JSCL.
## A fork of `http://lisa.sourceforge.net/`. Fossil Lisp code, ancient as mammoth's shit

#### Compilation only under web-repl (platform Electron)
```lisp
(setq bin #())
(load "00-prelude.lisp" :hook bin)
(load "01-utils.lisp" :hook bin)
(load "02-belief.lisp" :hook bin)
(load "03-reflect.lisp" :hook bin)
(load "04-core.lisp" :hook bin)
(load "05-rete.lisp" :hook bin)
(load "06-config.lisp" :hook bin :output "lisa.js")
```
Will be bundle js-code "lisa.js".

Compilation "lisa.js" look at `./bundle`.

### Use with browser

File `jscl.html`:

```html
    <script src="lisa.js" type="text/javascript"></script>
    <script src="jscl-web.js" type="text/javascript"></script>
```
```lisp
(deftemplate hobbit () 
    (slot name) (slot age))

(defrule r-1 ()
     (hobbit (name ?name) (age ?age))
=>
 (format t "Spawn hobbit ~a ~a ~%" ?name ?age))

(defrule r-2 ()
    (hobbit (name gendalf) (age 100))
=>
 (format t "Spawn wizard, ancient as mammoth's shit~%"))

(assert> (hobbit (name frodo)(age 30)))
(assert> (hobbit (name bilbo)(age 50)))
(assert> (hobbit (name gendalf)(age 100)))

```

Screenshot of LISA session ![general view](https://github.com/vlad-km/mlisa/blob/master/jscl.png)


### What's next

Read original documentation.
Have a fun.

##### As is, without any guarantees or obligations
