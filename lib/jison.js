// Jison, an LR(0), SLR(1), LARL(1), LR(1) Parser Generator
// Zachary Carter <zach@carter.name>
// MIT X Licensed

var typal      = require('./util/typal').typal;
var SillySet   = require('./util/set').Set;
var { mix, MixinBuilder } = require('./util/mixins');
var Lexer      = require('jison-lex');
var ebnfParser = require('ebnf-parser');
var JSONSelect = require('JSONSelect');
var esprima    = require('esprima');
var escodegen  = require('escodegen');
var assert     = require('node:assert');
var util       = require('node:util');


var version = require('../package.json').version;

var Jison = exports.Jison = exports;
Jison.version = version;
Jison.SillySet = SillySet;

// detect print
if (typeof console !== 'undefined' && console.log) {
    Jison.print = console.log;
} else if (typeof puts !== 'undefined') {
    Jison.print = function print () { puts([].join.call(arguments, ' ')); };
} else if (typeof print !== 'undefined') {
    Jison.print = print;
} else {
    Jison.print = function print () {};
}

Jison.Parser = (function () {

// iterator utility
function each (obj, func) {
    if (obj.forEach) {
        obj.forEach(func);
    } else {
        var p;
        for (p in obj) {
            if (obj.hasOwnProperty(p)) {
                func.call(obj, obj[p], p, obj);
            }
        }
    }
}

// var CanonicalCollection = Jison.CanonicalCollection = class CanonicalCollection {
//     constructor() {}
// };


var SymbolRegistry = Jison.SymbolRegistry = class SymbolRegistry {
    constructor() {
        this.mapping = new Map();
    }

    /// If the given argument hasn't been seen before, assign it a hash value equal to the current
    /// size of the map.
    tryRegisterNewSymbol(symbolString) {
        if (symbolString == null)
            return null;
        if (this.mapping.has(symbolString)) {
            return this.mapping.get(symbolString);
        }
        const symbolId = this.mapping.size;
        this.mapping.set(symbolString, symbolId);
        return symbolId;
    }
    getIdRegisteredForSymbol(symbolString) {
        return this.mapping.get(symbolString);
    }
    hasSeenThisSymbol(symbolString) {
        return this.mapping.has(symbolString);
    }

    [Symbol.iterator]() {
        return this.mapping.entries();
    }
    walkSymbolsWithIds() {
        return this[Symbol.iterator]();
    }

    /// Ignore all prior input and ensure the mapping reflects the desired identification for
    /// the given symbol.
    assignExplicitID(symbolString, desiredID) {
        return this.mapping.set(symbolString, desiredID);
    }
    /// Add the given args `symStrs` before re-adding the rest of the prior inputs, in the
    /// same order.
    unshiftWithPrefixIDs(...symStrs) {
        // Create indexed entries for the current args, starting from 0.
        const newPrefixWithKeys = new Array(symStrs.length);
        for (let i = 0; i < symStrs.length; ++i) {
            // Create index-tagged entries which Map converts into key-value associations in the
            // constructor.
            newPrefixWithKeys[i] = [symStrs[i], i];
        }
        // Splat ourselves back together!
        this.mapping = new Map([...newPrefixWithKeys, ...this.mapping]);
        // TODO: this doesn't reindex any existing entries, so there will be collisions; but from
        //       what I can tell that is exactly what we want here (to keep IDs valid, and with the
        //       expectation of hash collisions (more so than usual)).
        return this.mapping.size
    }
};

var NonterminalForest = Jison.NonterminalForest = class NonterminalForest {
    constructor() {
        this.bySymbol = new Map();
    }

    // Ensure this nonterminal is truly novel!
    emplaceNew(newNonterminal) {
        assert.ok(newNonterminal instanceof Nonterminal, newNonterminal);
        const { symbol } = newNonterminal;
        assert.ok(!this.bySymbol.has(symbol), symbol);
        this.bySymbol.set(symbol, newNonterminal);
        return this.bySymbol.get(symbol);
    }
    pushProductionForSymbol(symbol, production) {
        // console.dir({symbol, production});
        return this.bySymbol.get(symbol).productions.push(production);
    }
    pushFollowForSymbol(symbol, follow) {
        return this.bySymbol.get(symbol).follows.push(follow);
    }

    hasSeenThisSymbol(symString) {
        return this.bySymbol.has(symString);
    }
    getBySymbol(symString) {
        return this.bySymbol.get(symString)
    }
};

var ItemSet = Jison.ItemSet = class ItemSet {
    // How to get the hash key from an element.
    static idExtractor(item) {
        return item;
    }

    constructor(elements) {
        console.dir({elements});
        // FIXME: this could potentially just be a single Map instead of an array in concert with
        //        this.hash_ as a Set, but this formulation retains the *exact* behavior of the
        //        existing code (including subtleties about counting additional entries matching the
        //        same id). If we can figure out what these data structures are doing at some point,
        //        it should be safe to refactor them to use a single source of truth.
        this._items = [];

        // Stores `.id` of each element in ._items, which may repeat.
        this.hash_ = new Set;
        // Cached string value (which really shouldn't be cached...you'll see).
        this.stableDelimitedKeyString = null;

        if (elements == null) {
            return;
        }

        const id = this.constructor.idExtractor(elements);
        if (id != null && !Object.is(id, elements)) {
            // This is a single entry!
            this.push(elements);
            return;
        }

        // Try iterable.
        if (typeof elements[Symbol.iterator] === 'function') {
            this.concat(elements);
            return;
        }
    }

    validateKeyField(it) {
        const id = this.constructor.idExtractor(it);
        console.dir({k: (Object.keys(it)), it, id});
        if (typeof id != 'number') {
            throw new Error(`id extraction failed (from: '${it}')`);
        }
        return id;
    }
    tryPut(it) {
        const val = this.validateKeyField(it);
        return this.hash_.add(val);
    }

    // NB: we retain entries with the same id, not seeking to differentiate them at all.
    push(...items) {
        // console.dir({items});
        for (const it of items) {
            console.dir({it});
            this.tryPut(it);
            this._items.push(it);
        }
        return this._items.length;
    }
    // NB: This will mutate the caller of `this` and then return it!
    concat(set) {
        for (const item of set) {
            console.dir({item});
            this.push(item);
        }
        return this;
    }
    // drain()
    // NB: this will insert entries at the start!
    unshift(...items) {
        for (const it in items) {
            this.tryPut(it);
            this._items.unshift(it);
        }
        return this._items.length;
    }

    contains(item) {
        const val = this.validateKeyField(item);
        return this.hash_.has(val);
    }

    indexOf(item) {
        throw new Error('indexOf is never called!');
    }
    eq(set) {
        // return (this._items.length === set._items.length) && this.subset(set);
        throw new Error('eq is never called!');
    }

    union(set) {
        // TODO: this method in the original code does a couple very specific things:
        //       (1) does not modify `this` or expose anything that can be modified,
        //       (2) drops all the other this.xxx fields attached to this class.
        // return (new SillySet(this._items)).concat(this.complement(set));
        throw new Error('union is never called!');
    }
    intersection(set) {
        throw new Error('intersection is never called!');
    }
    complement(set) {
        throw new Error('complement is never called!');
    }
    subset(set) {
        throw new Error('subset is never called!');
    }
    superset(set) {
        throw new Error('superset is never called!');
    }

    // Strange accessor methods from the original code.
    // NB: These methods are written to have two arguments (`v, val`), but I think that's a result
    // of their generic prototypal library doing getter/setters, since the `val` is always ignored.
    item(v) {
        return this._items[v];
    }
    i(v) {
        return this._items[v];
    }
    first() {
        return this._items[0];
    }
    last() {
        return this._items[this._items.length - 1];
    }
    size() {
        return this._items.length;
    }
    isEmpty() {
        return this._items.length === 0;
    }

    forEach(callback) {
        return this._items.forEach(callback);
    }
    [Symbol.iterator]() {
        return this._items[Symbol.iterator]();
    }
    join(s) {
        return Array.from(this[Symbol.iterator]()).join(s);
    }


    copy() {
        throw new Error('copy is never called!');
    }
    toString() {
        return this._items.toString();
    }

    computeStableDelimitedKeyString() {
        // FIXME: it's unclear whether the original author intended to repeat the id for entries
        //        with the same id: since push/concat studiously avoids duplicating, I'm assuming
        //        that's intentional for some reason, so we retain the
        //        undocumented/unspecified/uncommented behavior here.
        // FIXME: this may be different behavior than before, but this entire code block appears to
        //        be dead code as well.
        return this._items
            .map((it) => { return this.constructor.idExtractor(it); })
            .sort()
            .join('|');
        // return this.hash_.keys().toArray().sort().join('|');
    }
    valueOf() {
        if (this.stableDelimitedKeyString != null) {
            throw new Error('caching value based on mutable data ???');
        }
        // FIXME: given that this is a mutable data structure, it's possible to add values to
        //        this._items after calling .valueOf() the first time. The original code reuses the
        //        cached value computed from the first time this method was called. It's possible
        //        that this is correct because ItemSets are never modified after calling .valueOf(),
        //        but since none of this is commented or documented, it may also just be a bug.
        return this.stableDelimitedKeyString ??= this.computeStableDelimitedKeyString();
        // var v = this._items.map(function (a) {return a.id;}).sort().join('|');
        // this.valueOf = function toValue_inner() {return v;};
        // return v;
    }
};

var IdFieldItemSet = Jison.IdFieldItemSet = class IdFieldItemSet extends ItemSet {
    static idExtractor(item) {
        return item.id;
    }
};

var ExtendedItemSet = Jison.ExtendedItemSet = class ExtendedItemSet extends IdFieldItemSet {
    constructor(elements) {
        super(elements)

        this.reductions = [];
        this.shifts = false;
        this.inadequate = false;

        this.goes = {};
        this.edges = {};
    }
};


var Nonterminal = Jison.Nonterminal = typal.construct({
    constructor: function Nonterminal (symbol) {
        this.symbol = symbol;
        this.productions = new Jison.IdFieldItemSet();
        this.first = [];
        this.follows = [];
        this.nullable = false;
    },
    toString: function Nonterminal_toString () {
        var str = this.symbol+"\n";
        str += (this.nullable ? 'nullable' : 'not nullable');
        str += "\nFirsts: "+this.first.join(', ');
        str += "\nFollows: "+this.first.join(', ');
        str += "\nProductions:\n  "+this.productions.join('\n  ');

        return str;
    }
});

var Production = typal.construct({
    constructor: function Production (symbol, handle, id) {
        this.symbol = symbol;
        this.handle = handle;
        this.nullable = false;
        this.id = id;
        this.first = [];
        this.precedence = 0;
    },
    toString: function Production_toString () {
        return this.symbol+" -> "+this.handle.join(' ');
    }
});

var generator = typal.beget();

generator.constructor = function Jison_Generator (grammar, opt) {
    if (typeof grammar === 'string') {
        grammar = ebnfParser.parse(grammar);
    }

    var options = typal.mix.call({}, grammar.options, opt);
    this.terms = {};
    this.operators = {};
    this.productions = [];
    this.conflicts = 0;
    this.resolutions = [];
    this.options = options;
    this.parseParams = grammar.parseParams;
    this.yy = {}; // accessed as yy free variable in the parser/lexer actions

    // source included in semantic action execution scope
    if (grammar.actionInclude) {
        if (typeof grammar.actionInclude === 'function') {
            grammar.actionInclude = String(grammar.actionInclude).replace(/^\s*function \(\) \{/, '').replace(/\}\s*$/, '');
        }
        this.actionInclude = grammar.actionInclude;
    }
    this.moduleInclude = grammar.moduleInclude || '';

    this.DEBUG = options.debug || false;
    if (this.DEBUG) this.mix(generatorDebug); // mixin debug methods

    this.processGrammar(grammar);

    if (grammar.lex) {
        this.lexer = new Lexer(grammar.lex, null, this.terminals_);
    }
};

generator.processGrammar = function processGrammarDef (grammar) {
    var bnf = grammar.bnf,
        tokens = grammar.tokens,
        nonterminals = this.nonterminals = new Jison.NonterminalForest(),
        productions = this.productions,
        self = this;

    if (!grammar.bnf && grammar.ebnf) {
        bnf = grammar.bnf = ebnfParser.transform(grammar.ebnf);
    }

    if (tokens) {
        if (typeof tokens === 'string') {
            tokens = tokens.trim().split(' ');
        } else {
            tokens = tokens.slice(0);
        }
    }

    var symbols = this.symbols = new Jison.SymbolRegistry();

    // calculate precedence of operators
    var operators = this.operators = processOperators(grammar.operators);

    // build productions from cfg
    this.buildProductions(bnf, productions, nonterminals, symbols, operators);

    if (tokens && this.terminals.length !== tokens.length) {
        self.trace("Warning: declared tokens differ from tokens found in rules.");
        self.trace(this.terminals);
        self.trace(tokens);
    }

    // augment the grammar
    this.augmentGrammar(grammar);
};

generator.augmentGrammar = function augmentGrammar (grammar) {
    console.dir({grammar, p: this.productions, s: this.startSymbol});
    if (this.productions.length === 0) {
        throw new Error("Grammar error: must have at least one rule.");
    }
    console.dir({gs: grammar.startSymbol, tp: this.productions.slice(5)});
    // use specified start symbol, or default to first user defined production
    this.startSymbol = grammar.start || grammar.startSymbol || this.productions[0].symbol;
    console.dir({ss: this.startSymbol});
    if (!this.nonterminals.hasSeenThisSymbol(this.startSymbol)) {
        throw new Error("Grammar error: startSymbol must be a non-terminal found in your grammar.");
    }
    this.EOF = "$end";

    // augment the grammar
    var acceptProduction = new Production('$accept', [this.startSymbol, '$end'], 0);
    this.productions.unshift(acceptProduction);

    // prepend parser tokens so that:
    // (1) these tokens come out first when iterating over symbols in order,
    // (2) '$accept' and this.EOF are specifically hashed to 0 and 1 (possibly/probably overlapping
    //     with the hashes of others, but this is not a problem at all).
    this.symbols.unshiftWithPrefixIDs("$accept", this.EOF);
    // NB: this will re-index this.EOF under 0! This may slightly differ from prior behavior!
    this.terminals.unshiftWithPrefixIDs(this.EOF);

    this.nonterminals
        .emplaceNew(new Nonterminal("$accept"))
        .productions
        .push(acceptProduction);

    // add follow $ to start symbol
    this.nonterminals.pushFollowForSymbol(this.startSymbol, this.EOF);
};

// set precedence and associativity of operators
function processOperators (ops) {
    if (!ops) return {};
    var operators = {};
    for (var i=0,k,prec;prec=ops[i]; i++) {
        for (k=1;k < prec.length;k++) {
            operators[prec[k]] = {precedence: i+1, assoc: prec[0]};
        }
    }
    return operators;
}


class ActionGroups {
    constructor() {
        this.byAction = new Map();
    }

    // Create a new list of labels for the action if not found, then append the current label.
    addActionLabel(action, label) {
        if (!this.byAction.has(action)) {
            this.byAction.set(action, []);
        }
        return this.byAction.get(action).push(label);
    }

    *iterAllRecordedActions() {
        for (const [actionName, allLabels] of this.byAction.entries()) {
            const joined = allLabels.join(' ');
            yield [joined, actionName, 'break;'];
        }
    }
    // NB: The prior version appears to add actions multiple times? Unless `actions` is deduplicated
    //     afterwards, the labels mapping to `action` will get reused.
    // for (const action in actionGroups)
    //   actions.push(actionGroups[action].join(' '), action, 'break;');
};


generator.stripAliases = function stripAliases(rhs) {
    return rhs.map((e) => e.replace(/\[[a-zA-Z_][a-zA-Z0-9_-]*\]/g, ''));
};


generator.compileNextProduction = function compileNextProduction(handle) {
    console.dir({handle, h: handle.length, i: typeof handle[1]}, { depth: null });

    if (!Array.isArray(handle)) {
        // no action -> don't care about aliases; strip them.
        // !!!! NB: swap these two lines like the other cases. same effect but more correct
        // handle = handle.replace(/\[[a-zA-Z_][a-zA-Z0-9_-]*\]/g, '');
        const rhs = handle.trim().split(' ');
        return {rhs};
    }

    const rhs = (typeof handle[0] === 'string') ?
          handle[0].trim().split(' ') :
          handle[0].slice(0);

    if (handle.length < 3) {
        assert.notEqual(typeof handle[1], 'string');
        const operator = handle[1];
        return {rhs, operator};
    }

    // Need to do more work for semantic actions!
    const [action, operator] = handle.slice(1);
    assert.ok(action != null);
    // precedence specified also
    return {rhs, action, operator}
};

// semantic action specified
generator.processSemanticActions = function processSemanticActions(rhs, action) {
    // replace named semantic values ($nonterminal)
    if (action.match(/[$@][a-zA-Z][a-zA-Z0-9_]*/)) {
        const count = new Map;
        const names = new Map;

        for (let i = 0; i < rhs.length; i++) {
            let symString = rhs[i];
            // check for aliased names, e.g., id[alias]
            let rhs_i = symString.match(/\[[a-zA-Z][a-zA-Z0-9_-]*\]/);
            if (rhs_i) {
                // TODO: ???
                rhs_i = rhs_i[0].substr(1, rhs_i[0].length - 2);
                symString = symString.substr(0, symString.indexOf('['));
            } else {
                rhs_i = symString;
            }

            // TODO: no clue what this does!
            if (names.has(rhs_i)) {
                // NB: Need to put this on a separate line to use ++c.
                const c = count.get(rhs_i);
                names.set((rhs_i + (++c)),
                          (i + 1));
            } else {
                names.set((rhs_i),
                          (i + 1));
                names.set((rhs_i + "1"),
                          (i + 1));
                count.set(rhs_i, 1);
            }
        }

        action = action.replace(/\$([a-zA-Z][a-zA-Z0-9_]*)/g, function (str, pl) {
            return names.get(pl) ? '$'+names.get(pl) : str;
        }).replace(/@([a-zA-Z][a-zA-Z0-9_]*)/g, function (str, pl) {
            return names.get(pl) ? '@'+names.get(pl) : str;
        });
    }
    // (1) replace references to $$ with this.$, and @$ with this._$
    // (2) replace semantic value references ($n) with stack value (stack[n])
    // (3) same as above for location references (@n)
    action = action.replace(/([^'"])\$\$|^\$\$/g, '$1this.$').replace(/@[0$]/g, "this._$")
        .replace(/\$(-?\d+)/g, function (_, n) {
            return "$$[$0" + (parseInt(n, 10) - rhs.length || '') + "]";
        })
        .replace(/@(-?\d+)/g, function (_, n) {
            return "_$[$0" + (n - rhs.length || '') + "]";
        });

    // console.dir({action, actionGroups});
    // actionGroups.addActionLabel(action, label);
    return action;
};

generator.processProductionVariants = function processProductionVariants(parsedProduction, curSymbol) {
    const { rhs, operator, action } = parsedProduction;

    // Register any new symbols found.
    for (const symString of rhs) {
        if (symString === 'error') {
            this.hasErrorRecovery = true;
            // TODO: original author had a very confusing error flag here!
            // throw new Error('found error symbol')
        }
        this.symbols.tryRegisterNewSymbol(symString);
    }

    const curProdId = this.productions.length + 1

    // Semantic action is the hard stuff. Let's see if we have to do that here.
    if (action != null) {
        const label = `case ${curProdId}:`;
        // const label = 'case ' + (this.productions.length + 1) + ':';
        const processedAction = this.processSemanticActions(rhs, action);
        // console.dir({label, action, processedAction});
        this.actionGroups.addActionLabel(processedAction, label);
    }

    // (done with aliases; strip them.)
    const stripped = this.stripAliases(rhs);
    console.dir({rhs, stripped});

    // The new production is here!!!
    const r = new Production(curSymbol, stripped, curProdId);

    // Propagate over some operator precedence (these rules are weird and unexplained!!)!
    const operatorSpecification = this.operators[operator?.prec];
    if (operatorSpecification != null) {
        r.precedence = operatorSpecification.precedence;
    }
    if (r.precedence === 0) {
        for (let i = r.handle.length - 1; i >= 0; i--) {
            const curOp = r.handle[i];
            if (!this.nonterminals.hasSeenThisSymbol(curOp)) {
                // TODO: this may just be `this.operators[curOp]` instead? probably not?
                const operatorSpecification = this.operators[curOp?.prec];
                if (operatorSpecification != null) {
                    r.precedence = operatorSpecification.precedence;
                }
            }
        }
    }

    // Register it with all the mutable state.
    this.productions.push(r);
    this.productions_.push([
        this.symbols.getIdRegisteredForSymbol(r.symbol),
        // TODO: absolutely no clue what either of these are for or otherwise signify.
        r.handle[0] === '' ? 0 : r.handle.length,
    ]);
    this.nonterminals.pushProductionForSymbol(curSymbol, r);

    return r;
};

generator.buildProductions = function buildProductions(bnf, productions, nonterminals, symbols, operators) {
    const actions = [
      '/* this == yyval */',
      this.actionInclude || '',
      'var $0 = $$.length - 1;',
      'switch (yystate) {'
    ];
    // NB: This needs to be declared as an instance property earlier because it's used in
    //     processProductionVariants/etc!
    this.actionGroups = new ActionGroups();
    // var productions_ = [0];
    // console.dir({operators, symbols});
    this.productions_ = [0]

    var her = false; // has error recovery

    // add error symbol; will be third symbol, or "2" ($accept, $end, error)
    symbols.tryRegisterNewSymbol("error");

    console.dir({bnf, symbols, nonterminals, productions, operators});
    for (const symbol of Object.getOwnPropertyNames(bnf)) {
        console.dir({symbol});

        symbols.tryRegisterNewSymbol(symbol);
        nonterminals.emplaceNew(new Nonterminal(symbol));
        console.dir({symbols, nonterminals});

        let prods = bnf[symbol];
        if (typeof prods === 'string') {
            prods = prods.split(/\s*\|\s*/g);
        } else {
            prods = prods.slice(0);
        }

        console.dir({prods});
        for (const handle of prods) {
            const parsedProduction = this.compileNextProduction(handle);
            const newProd = this.processProductionVariants(parsedProduction, symbol);
            console.dir({handle, parsedProduction, newProd});
        }
        // In the original code, this passes `symbol` into the closure env via `var`.
        // prods.forEach((handle) => this.compileNextProduction(handle, actionGroups));
    }

    // TODO: we could possibly just push all the values together at once, but this is how the
    // previous code did it.
    for (const [joined, base, breakCase] of this.actionGroups.iterAllRecordedActions()) {
        actions.push(joined, base, breakCase);
    }
    actions.push('}');
    // NB: This is consumed by `this.performAction` below.
    const compiledActions = actions.join("\n")
          .replace(/YYABORT/g, 'return false')
          .replace(/YYACCEPT/g, 'return true');

    const terms = new Jison.SymbolRegistry();

    for (const [sym, id] of symbols.walkSymbolsWithIds()) {
        if (!nonterminals.hasSeenThisSymbol(sym)) {
            assert.ok(!terms.hasSeenThisSymbol(sym));
            terms.assignExplicitID(sym, id);
        }
    }

    this.terminals = terms

    this.hasErrorRecovery = her;

    let parameters = "yytext, yyleng, yylineno, yy, yystate /* action[1] */, $$ /* vstack */, _$ /* lstack */";
    if (this.parseParams) parameters += ', ' + this.parseParams.join(', ');

    this.performAction = "function anonymous(" + parameters + ") {\n" + compiledActions + "\n}";
};



generator.createParser = function createParser () {
    throw new Error('Calling abstract method.');
};

// noop. implemented in debug mixin
generator.trace = function trace () { };

generator.warn = function warn () {
    var args = Array.prototype.slice.call(arguments,0);
    Jison.print.call(null,args.join(""));
};

generator.error = function error (msg) {
    throw new Error(msg);
};

// Generator debug mixin

var generatorDebug = {
    trace: function trace () {
        Jison.print.apply(null, arguments);
    },
    beforeprocessGrammar: function () {
        this.trace("Processing grammar.");
    },
    afteraugmentGrammar: function () {
        var trace = this.trace;
        each(this.symbols, function (sym, i) {
            trace(sym+"("+i+")");
        });
    }
};



/*
 * Mixin for common behaviors of lookahead parsers
 * */
var lookaheadMixin = {};


lookaheadMixin.computeLookaheads = function computeLookaheads () {
    if (this.DEBUG) this.mix(lookaheadDebug); // mixin debug methods

    this.computeLookaheads = function () {};
    this.nullableSets();
    this.firstSets();
    this.followSets();
};

// calculate follow sets typald on first and nullable
lookaheadMixin.followSets = function followSets () {
    var productions = this.productions,
        nonterminals = this.nonterminals,
        self = this,
        cont = true;

    // loop until no further changes have been made
    while(cont) {
        cont = false;

        productions.forEach(function Follow_prod_forEach (production, k) {
            //self.trace(production.symbol,nonterminals[production.symbol].follows);
            // q is used in Simple LALR algorithm determine follows in context
            var q;
            var ctx = !!self.go_;

            var set = [],oldcount;
            for (var i=0,t;t=production.handle[i];++i) {
                if (!nonterminals[t]) continue;

                // for Simple LALR algorithm, self.go_ checks if
                // FIXME: IF WHAT???
                if (ctx)
                    q = self.go_(production.symbol, production.handle.slice(0, i));
                var bool = !ctx || q === parseInt(self.nterms_[t], 10);

                if (i === production.handle.length+1 && bool) {
                    set = nonterminals[production.symbol].follows;
                } else {
                    var part = production.handle.slice(i+1);

                    set = self.first(part);
                    if (self.nullable(part) && bool) {
                        set.push.apply(set, nonterminals[production.symbol].follows);
                    }
                }
                oldcount = nonterminals[t].follows.length;
                // (2)FIXME: this is so slow!
                SillySet.union(nonterminals[t].follows, set);
                if (oldcount !== nonterminals[t].follows.length) {
                    cont = true;
                }
            }
        });
    }
};


// return the FIRST set of a symbol or series of symbols
lookaheadMixin.first = function first (symbol) {
    // epsilon
    if (symbol === '') {
        return [];
    // RHS
    } else if (symbol instanceof Array) {
        var firsts = [];
        for (var i=0,t;t=symbol[i];++i) {
            if (!this.nonterminals[t]) {
                if (firsts.indexOf(t) === -1)
                    firsts.push(t);
            } else {
                SillySet.union(firsts, this.nonterminals[t].first);
            }
            if (!this.nullable(t))
                break;
        }
        return firsts;
    // terminal
    } else if (!this.nonterminals[symbol]) {
        return [symbol];
    // nonterminal
    } else {
        return this.nonterminals[symbol].first;
    }
};


// fixed-point calculation of FIRST sets
lookaheadMixin.firstSets = function firstSets () {
    var productions = this.productions,
        nonterminals = this.nonterminals,
        self = this,
        cont = true,
        symbol,firsts;

    // loop until no further changes have been made
    while(cont) {
        cont = false;

        productions.forEach(function FirstSets_forEach (production, k) {
            var firsts = self.first(production.handle);
            if (firsts.length !== production.first.length) {
                production.first = firsts;
                cont=true;
            }
        });

        for (symbol in nonterminals) {
            firsts = [];
            nonterminals[symbol].productions.forEach(function (production) {
                SillySet.union(firsts, production.first);
            });
            if (firsts.length !== nonterminals[symbol].first.length) {
                nonterminals[symbol].first = firsts;
                cont=true;
            }
        }
    }
};

// fixed-point calculation of NULLABLE
lookaheadMixin.nullableSets = function nullableSets () {
    var firsts = this.firsts = {},
        nonterminals = this.nonterminals,
        self = this,
        cont = true;

    // loop until no further changes have been made
    while(cont) {
        cont = false;

        // check if each production is nullable
        this.productions.forEach(function (production, k) {
            if (!production.nullable) {
                for (var i=0,n=0,t;t=production.handle[i];++i) {
                    if (self.nullable(t)) n++;
                }
                if (n===i) { // production is nullable if all tokens are nullable
                    production.nullable = cont = true;
                }
            }
        });

        //check if each symbol is nullable
        for (var symbol in nonterminals) {
            if (!this.nullable(symbol)) {
                for (var i=0,production;production=nonterminals[symbol].productions.item(i);i++) {
                    if (production.nullable)
                        nonterminals[symbol].nullable = cont = true;
                }
            }
        }
    }
};

// check if a token or series of tokens is nullable
lookaheadMixin.nullable = function nullable (symbol) {
    // epsilon
    if (symbol === '') {
        return true;
    // RHS
    } else if (symbol instanceof Array) {
        for (var i=0,t;t=symbol[i];++i) {
            if (!this.nullable(t))
                return false;
        }
        return true;
    // terminal
    } else if (!this.nonterminals[symbol]) {
        return false;
    // nonterminal
    } else {
        return this.nonterminals[symbol].nullable;
    }
};


// lookahead debug mixin
var lookaheadDebug = {
    beforenullableSets: function () {
        this.trace("Computing Nullable sets.");
    },
    beforefirstSets: function () {
        this.trace("Computing First sets.");
    },
    beforefollowSets: function () {
        this.trace("Computing Follow sets.");
    },
    afterfollowSets: function () {
        var trace = this.trace;
        each(this.nonterminals, function (nt, t) {
            trace(nt, '\n');
        });
    }
};

/*
 * Mixin for common LR parser behavior
 * */
var lrGeneratorMixin = {};
lrGeneratorMixin.ItemSet = Jison.ItemSet;
lrGeneratorMixin.IdFieldItemSet = Jison.IdFieldItemSet;
lrGeneratorMixin.ExtendedItemSet = Jison.ExtendedItemSet;


lrGeneratorMixin.buildTable = function buildTable () {
    if (this.DEBUG) this.mix(lrGeneratorDebug); // mixin debug methods

    this.states = this.canonicalCollection();
    this.table = this.parseTable(this.states);
    this.defaultActions = findDefaults(this.table);
};

lrGeneratorMixin.Item = typal.construct({
    constructor: function Item(production, dot, f, predecessor) {
        console.dir({production, dot, f, predecessor});
        this.production = production;
        this.dotPosition = dot || 0;
        this.follows = f || [];
        this.predecessor = predecessor;
        this.id = parseInt(production.id+'a'+this.dotPosition, 36);
        this.markedSymbol = this.production.handle[this.dotPosition];
    },
    remainingHandle: function () {
        return this.production.handle.slice(this.dotPosition+1);
    },
    eq: function (e) {
        return e.id === this.id;
    },
    handleToString: function () {
        var handle = this.production.handle.slice(0);
        handle[this.dotPosition] = '.'+(handle[this.dotPosition]||'');
        return handle.join(' ');
    },
    toString: function () {
        var temp = this.production.handle.slice(0);
        temp[this.dotPosition] = '.'+(temp[this.dotPosition]||'');
        return this.production.symbol+" -> "+temp.join(' ') +
            (this.follows.length === 0 ? "" : " #lookaheads= "+this.follows.join(' '));
    }
});


lrGeneratorMixin.curItemQueue = function* curItemQueue (itemSetArg) {
    const itemSet = itemSetArg;

    // (1) Read from the given `itemSet` while pushing anything new to `itemQueue`.
    for (const item of itemSet[Symbol.iterator]()) {
        const { markedSymbol: symbol } = item;
        const nt = this.nonterminals.getBySymbol(symbol);
        yield {symbol, item, nt}
    }
};

lrGeneratorMixin.cycleQueue = function* cycleQueue (itemQueue) {
    // const itemQueue = [];

    // (2) Read asynchronously from cyclic `itemQueue` results.
    while (itemQueue.length > 0) {
        // NB: mutate `itemQueue` to take all the new entries!
        const newItems = itemQueue.splice(0, itemQueue.length);

        // FIXME: remove repeated code from above!
        for (const item of newItems) {
            const { markedSymbol: symbol } = item;
            const nt = this.nonterminals.getBySymbol(symbol);
            yield {symbol, item, nt}
        }
    }
};


lrGeneratorMixin.closureQueue = function* closureQueue (itemSetArg, closureSet) {
    const itemQueue = [];
    const syms = new Set();

    const curItems = this.curItemQueue(itemSetArg);
    const cycleItems = this.cycleQueue(itemQueue);

    // Use IIFE (immediately-invoked function expressions) to address some scoping concerns:
    const chain = (function(a, b) { // still returning a function!
        (function* (itemSetArg, itemQueue, closureSet) {
            try {
                yield* a;
                yield* b;
            } catch (e) {
                console.dir({e});
                console.dir({itemSetArg, closureSet});
                throw e;
            }
        })(itemSetArg, itemQueue, closureSet)
    });

    for (const {symbol, item, nt} in chain(curItems, cycleItems)) {
        console.log({symbol, item, nt});
        yield {symbol, item, nt};
    }
};

// NB: Yet another extremely complex and undocumented process. Even just a vague description of
// what you were going for! This is so difficult to read!
lrGeneratorMixin.closureOperation = function closureOperation (itemSetArg, closureSetArg) {
    // TODO: previously was just Set, not ItemSet?
    const closureSet = closureSetArg ?? new this.ExtendedItemSet();

    const itemSet = itemSetArg;
    const syms = new Set();

    console.dir({closureSet, itemSet});

    // NB: This line will do several things you might not be expecting:
    //     (1) `itemSet` is iterated over but not modified in any way.
    //     (2) `hash_` will be updated with all new entries from `itemSet`, but:
    //     (3) `_items` will still add all items to the underlying array (no overlap check is
    //         performed).
    closureSet.concat(itemSet);

    for (const {symbol, item, nt} of this.closureQueue(itemSet, closureSet)) {
        console.dir({symbol, item, nt});

        // if token is a non-terminal, recursively add closures
        if (symbol && (nt != null)) {
            if(!syms.has(symbol)) {
                for (const production of nt.productions) {
                    const newItem = new this.Item(production, 0);
                    if(!closureSet.contains(newItem)) {
                        itemQueue.push(newItem);
                    }
                }
                syms.add(symbol);
            }
        } else if (!symbol) {
            // TODO: what do these mean?
            // reduction
            closureSet.reductions.push(item);
            closureSet.inadequate = closureSet.reductions.length > 1 || closureSet.shifts;
        } else {
            // TODO: what do these mean?
            // shift
            closureSet.shifts = true;
            closureSet.inadequate = closureSet.reductions.length > 0;
        }
    }

    return closureSet;
};


// NB: no clue what this is doing and no comments to explain, sigh...
lrGeneratorMixin.gotoOperation = function gotoOperation (itemSet, symbol) {
    var gotoSet = new this.ExtendedItemSet(),
        self = this;

    
    console.dir({itemSet, symbol}, { depth: 3 });
    itemSet.forEach(function goto_forEach(item, n) {
        // TODO: optimization opportunity? cache against symbols? figure out what this is doing
        //       first!
        console.dir({gotoItem: item, n});
        throw new Error('ok');
        if (item.markedSymbol === symbol) {
            gotoSet.push(new self.Item(item.production, item.dotPosition+1, item.follows, n));
        }
    });

    return gotoSet.isEmpty() ? gotoSet : this.closureOperation(gotoSet);
};

/* Create unique set of item sets
 * */
lrGeneratorMixin.canonicalCollection = function canonicalCollection () {
    const item1 = new this.Item(this.productions[0], 0, [this.EOF]);
    const idSet = new this.IdFieldItemSet([item1]);
    const firstState = this.closureOperation(idSet);
    console.dir({firstState, idSet, item1}, {depth: null});

    const states = new this.IdFieldItemSet(firstState);
    const self = this;
    let itemSet;

    console.dir({sh: states});
    // (1)FIXME: new class for this!
    states.has = {};
    states.has[firstState] = 0;

    console.dir({
        ss: states.size(),
        firstState,
        item1,
    }, { depth: 3 });

    let marked = 0;
    while (marked !== states.size()) {
        assert.ok(marked <= states.size());
        console.dir({marked, ss: states.size()});
        console.error(`marked = ${marked}`);
        console.dir({states});
        console.dir({marked, s111: states.size()}, { depth: null });

        itemSet = states.item(marked);
        marked++;

        // console.dir({itemSet, si: states.item}, { depth: 2 });
        // console.info(util.inspect(itemSet, {showHidden: true, colors: true}));
        if (typeof itemSet.forEach === 'function') {
            itemSet.forEach(function CC_itemSet_forEach (item) {
                if (item.markedSymbol && item.markedSymbol !== self.EOF) {
                    self.canonicalCollectionInsert(item.markedSymbol, itemSet, states, marked - 1);
                }
            });
        }
    }

    return states;
};


lrGeneratorMixin.JJJ = Jison.JJJ = (superclass) => class JJJ extends superclass {
    // FIXME: .has!
    constructor(...x) {
        super(...x);
        this.seen = new Map();
        this.predecessors ??= new Map();
    }

    register(state) {
        // FIXME: this was set in the prior version of the code, but it's not clear where or how or
        //        even if it propagates. Figure this out!
        this.seen.set(state, 0);
    }


};

// Pushes a unique state into the que. Some parsing algorithms may perform additional operations
lrGeneratorMixin.canonicalCollectionInsert = function canonicalCollectionInsert (symbol, itemSet, states, stateNum) {
    const g = this.gotoOperation(itemSet, symbol);
    g.predecessors ??= {}
    // add g to que if not empty or duplicate
    if (!g.isEmpty()) {
        // TODO: this is an expensive and possibly unsound operation.
        const gv = g.valueOf();
        console.dir({g, gv});
        let i = states.has[gv];
        // TODO: why -1 here? when would that ever happen?
        if (i === -1 || typeof i === 'undefined') {
            if (i === -1) {
                throw new Error('ok2');
            }
            states.has[gv] = states.size();
            itemSet.edges[symbol] = states.size(); // store goto transition for table
            states.push(g);
            g.predecessors[symbol] = [stateNum];
        } else {
            itemSet.edges[symbol] = i; // store goto transition for table
            states.item(i).predecessors[symbol].push(stateNum);
        }
    }
};

var NONASSOC = 0;
lrGeneratorMixin.parseTable = function parseTable (itemSets) {
    var states = [],
        nonterminals = this.nonterminals,
        operators = this.operators,
        conflictedStates = {}, // array of [state, token] tuples
        self = this,
        s = 1, // shift
        r = 2, // reduce
        a = 3; // accept

    // for each item set
    itemSets.forEach(function (itemSet, k) {
        var state = states[k] = {};
        var action, stackSymbol;

        // set shift and goto actions
        for (stackSymbol in itemSet.edges) {
            itemSet.forEach(function (item, j) {
                // find shift and goto actions
                if (item.markedSymbol == stackSymbol) {
                    var gotoState = itemSet.edges[stackSymbol];
                    if (nonterminals[stackSymbol]) {
                        // store state to go to after a reduce
                        //self.trace(k, stackSymbol, 'g'+gotoState);
                        state[self.symbols_[stackSymbol]] = gotoState;
                    } else {
                        //self.trace(k, stackSymbol, 's'+gotoState);
                        state[self.symbols_[stackSymbol]] = [s,gotoState];
                    }
                }
            });
        }

        // set accept action
        itemSet.forEach(function (item, j) {
            if (item.markedSymbol == self.EOF) {
                // accept
                state[self.symbols_[self.EOF]] = [a];
                //self.trace(k, self.EOF, state[self.EOF]);
            }
        });

        var allterms = self.lookAheads ? false : self.terminals;

        // set reductions and resolve potential conflicts
        itemSet.reductions.forEach(function (item, j) {
            // if parser uses lookahead, only enumerate those terminals
            var terminals = allterms || self.lookAheads(itemSet, item);

            terminals.forEach(function (stackSymbol) {
                action = state[self.symbols_[stackSymbol]];
                var op = operators[stackSymbol];

                // Reading a terminal and current position is at the end of a production, try to reduce
                if (action || action && action.length) {
                    var sol = resolveConflict(item.production, op, [r,item.production.id], action[0] instanceof Array ? action[0] : action);
                    self.resolutions.push([k,stackSymbol,sol]);
                    if (sol.bydefault) {
                        self.conflicts++;
                        if (!self.DEBUG) {
                            self.warn('Conflict in grammar: multiple actions possible when lookahead token is ',stackSymbol,' in state ',k, "\n- ", printAction(sol.r, self), "\n- ", printAction(sol.s, self));
                            conflictedStates[k] = true;
                        }
                        if (self.options.noDefaultResolve) {
                            if (!(action[0] instanceof Array))
                                action = [action];
                            action.push(sol.r);
                        }
                    } else {
                        action = sol.action;
                    }
                } else {
                    action = [r,item.production.id];
                }
                if (action && action.length) {
                    state[self.symbols_[stackSymbol]] = action;
                } else if (action === NONASSOC) {
                    state[self.symbols_[stackSymbol]] = undefined;
                }
            });
        });

    });

    if (!self.DEBUG && self.conflicts > 0) {
        self.warn("\nStates with conflicts:");
        each(conflictedStates, function (val, state) {
            self.warn('State '+state);
            self.warn('  ',itemSets.item(state).join("\n  "));
        });
    }

    return states;
};

// find states with only one action, a reduction
function findDefaults (states) {
    var defaults = {};
    states.forEach(function (state, k) {
        var i = 0;
        for (var act in state) {
             if ({}.hasOwnProperty.call(state, act)) i++;
        }

        if (i === 1 && state[act][0] === 2) {
            // only one action in state and it's a reduction
            defaults[k] = state[act];
        }
    });

    return defaults;
}

// resolves shift-reduce and reduce-reduce conflicts
function resolveConflict (production, op, reduce, shift) {
    var sln = {production: production, operator: op, r: reduce, s: shift},
        s = 1, // shift
        r = 2, // reduce
        a = 3; // accept

    if (shift[0] === r) {
        sln.msg = "Resolve R/R conflict (use first production declared in grammar.)";
        sln.action = shift[1] < reduce[1] ? shift : reduce;
        if (shift[1] !== reduce[1]) sln.bydefault = true;
        return sln;
    }

    if (production.precedence === 0 || !op) {
        sln.msg = "Resolve S/R conflict (shift by default.)";
        sln.bydefault = true;
        sln.action = shift;
    } else if (production.precedence < op.precedence ) {
        sln.msg = "Resolve S/R conflict (shift for higher precedent operator.)";
        sln.action = shift;
    } else if (production.precedence === op.precedence) {
        if (op.assoc === "right" ) {
            sln.msg = "Resolve S/R conflict (shift for right associative operator.)";
            sln.action = shift;
        } else if (op.assoc === "left" ) {
            sln.msg = "Resolve S/R conflict (reduce for left associative operator.)";
            sln.action = reduce;
        } else if (op.assoc === "nonassoc" ) {
            sln.msg = "Resolve S/R conflict (no action for non-associative operator.)";
            sln.action = NONASSOC;
        }
    } else {
        sln.msg = "Resolve conflict (reduce for higher precedent production.)";
        sln.action = reduce;
    }

    return sln;
}

lrGeneratorMixin.generate = function parser_generate (opt) {
    opt = typal.mix.call({}, this.options, opt);
    var code = "";

    // check for illegal identifier
    if (!opt.moduleName || !opt.moduleName.match(/^[A-Za-z_$][A-Za-z0-9_$]*$/)) {
        opt.moduleName = "parser";
    }
    switch (opt.moduleType) {
        case "js":
            code = this.generateModule(opt);
            break;
        case "amd":
            code = this.generateAMDModule(opt);
            break;
        default:
            code = this.generateCommonJSModule(opt);
            break;
    }

    return code;
};

lrGeneratorMixin.generateAMDModule = function generateAMDModule(opt){
    opt = typal.mix.call({}, this.options, opt);
    var module = this.generateModule_();
    var out = '\n\ndefine(function(require){\n'
        + module.commonCode
        + '\nvar parser = '+ module.moduleCode
        + "\n"+this.moduleInclude
        + (this.lexer && this.lexer.generateModule ?
          '\n' + this.lexer.generateModule() +
          '\nparser.lexer = lexer;' : '')
        + '\nreturn parser;'
        + '\n});'
    return out;
};

lrGeneratorMixin.generateCommonJSModule = function generateCommonJSModule (opt) {
    opt = typal.mix.call({}, this.options, opt);
    var moduleName = opt.moduleName || "parser";
    var out = this.generateModule(opt)
        + "\n\n\nif (typeof require !== 'undefined' && typeof exports !== 'undefined') {"
        + "\nexports.parser = "+moduleName+";"
        + "\nexports.Parser = "+moduleName+".Parser;"
        + "\nexports.parse = function () { return "+moduleName+".parse.apply("+moduleName+", arguments); };"
        + "\nexports.main = "+ String(opt.moduleMain || commonjsMain) + ";"
        + "\nif (typeof module !== 'undefined' && require.main === module) {\n"
        + "  exports.main(process.argv.slice(1));\n}"
        + "\n}";

    return out;
};

lrGeneratorMixin.generateModule = function generateModule (opt) {
    opt = typal.mix.call({}, this.options, opt);
    var moduleName = opt.moduleName || "parser";
    var out = "/* parser generated by jison " + version + " */\n"
        + "/*\n"
        + "  Returns a Parser object of the following structure:\n"
        + "\n"
        + "  Parser: {\n"
        + "    yy: {}\n"
        + "  }\n"
        + "\n"
        + "  Parser.prototype: {\n"
        + "    yy: {},\n"
        + "    trace: function(),\n"
        + "    symbols_: {associative list: name ==> number},\n"
        + "    terminals_: {associative list: number ==> name},\n"
        + "    productions_: [...],\n"
        + "    performAction: function anonymous(yytext, yyleng, yylineno, yy, yystate, $$, _$),\n"
        + "    table: [...],\n"
        + "    defaultActions: {...},\n"
        + "    parseError: function(str, hash),\n"
        + "    parse: function(input),\n"
        + "\n"
        + "    lexer: {\n"
        + "        EOF: 1,\n"
        + "        parseError: function(str, hash),\n"
        + "        setInput: function(input),\n"
        + "        input: function(),\n"
        + "        unput: function(str),\n"
        + "        more: function(),\n"
        + "        less: function(n),\n"
        + "        pastInput: function(),\n"
        + "        upcomingInput: function(),\n"
        + "        showPosition: function(),\n"
        + "        test_match: function(regex_match_array, rule_index),\n"
        + "        next: function(),\n"
        + "        lex: function(),\n"
        + "        begin: function(condition),\n"
        + "        popState: function(),\n"
        + "        _currentRules: function(),\n"
        + "        topState: function(),\n"
        + "        pushState: function(condition),\n"
        + "\n"
        + "        options: {\n"
        + "            ranges: boolean           (optional: true ==> token location info will include a .range[] member)\n"
        + "            flex: boolean             (optional: true ==> flex-like lexing behaviour where the rules are tested exhaustively to find the longest match)\n"
        + "            backtrack_lexer: boolean  (optional: true ==> lexer regexes are tested in order and for each matching regex the action code is invoked; the lexer terminates the scan when a token is returned by the action code)\n"
        + "        },\n"
        + "\n"
        + "        performAction: function(yy, yy_, $avoiding_name_collisions, YY_START),\n"
        + "        rules: [...],\n"
        + "        conditions: {associative list: name ==> set},\n"
        + "    }\n"
        + "  }\n"
        + "\n"
        + "\n"
        + "  token location info (@$, _$, etc.): {\n"
        + "    first_line: n,\n"
        + "    last_line: n,\n"
        + "    first_column: n,\n"
        + "    last_column: n,\n"
        + "    range: [start_number, end_number]       (where the numbers are indexes into the input string, regular zero-based)\n"
        + "  }\n"
        + "\n"
        + "\n"
        + "  the parseError function receives a 'hash' object with these members for lexer and parser errors: {\n"
        + "    text:        (matched text)\n"
        + "    token:       (the produced terminal token, if any)\n"
        + "    line:        (yylineno)\n"
        + "  }\n"
        + "  while parser (grammar) errors will also provide these members, i.e. parser errors deliver a superset of attributes: {\n"
        + "    loc:         (yylloc)\n"
        + "    expected:    (string describing the set of expected tokens)\n"
        + "    recoverable: (boolean: TRUE when the parser has a error recovery rule available for this particular error)\n"
        + "  }\n"
        + "*/\n";
    out += (moduleName.match(/\./) ? moduleName : "var "+moduleName) +
            " = " + this.generateModuleExpr();

    return out;
};


lrGeneratorMixin.generateModuleExpr = function generateModuleExpr () {
    var out = '';
    var module = this.generateModule_();

    out += "(function(){\n";
    out += module.commonCode;
    out += "\nvar parser = "+module.moduleCode;
    out += "\n"+this.moduleInclude;
    if (this.lexer && this.lexer.generateModule) {
        out += this.lexer.generateModule();
        out += "\nparser.lexer = lexer;";
    }
    out += "\nfunction Parser () {\n  this.yy = {};\n}\n"
        + "Parser.prototype = parser;"
        + "parser.Parser = Parser;"
        + "\nreturn new Parser;\n})();";

    return out;
};

function addTokenStack (fn) {
    var parseFn = fn;
    try {
        var ast = esprima.parse(parseFn);
        var stackAst = esprima.parse(String(tokenStackLex)).body[0];
        stackAst.id.name = 'lex';

        var labeled = JSONSelect.match(':has(:root > .label > .name:val("_token_stack"))', ast);

        labeled[0].body = stackAst;

        return escodegen.generate(ast).replace(/_token_stack:\s?/,"").replace(/\\\\n/g,"\\n");
    } catch (e) {
        return parseFn;
    }
}

// lex function that supports token stacks
function tokenStackLex() {
    var token;
    token = tstack.pop() || lexer.lex() || EOF;
    // if token isn't its numeric value, convert
    if (typeof token !== 'number') {
        if (token instanceof Array) {
            tstack = token;
            token = tstack.pop();
        }
        token = self.symbols_[token] || token;
    }
    return token;
}

// returns parse function without error recovery code
function removeErrorRecovery (fn) {
    var parseFn = fn;
    try {
        var ast = esprima.parse(parseFn);

        var labeled = JSONSelect.match(':has(:root > .label > .name:val("_handle_error"))', ast);
        var reduced_code = labeled[0].body.consequent.body[3].consequent.body;
        reduced_code[0] = labeled[0].body.consequent.body[1];     // remove the line: error_rule_depth = locateNearestErrorRecoveryRule(state);
        reduced_code[4].expression.arguments[1].properties.pop(); // remove the line: 'recoverable: error_rule_depth !== false'
        labeled[0].body.consequent.body = reduced_code;

        return escodegen.generate(ast).replace(/_handle_error:\s?/,"").replace(/\\\\n/g,"\\n");
    } catch (e) {
        return parseFn;
    }
}

// Generates the code of the parser module, which consists of two parts:
// - module.commonCode: initialization code that should be placed before the module
// - module.moduleCode: code that creates the module object
lrGeneratorMixin.generateModule_ = function generateModule_ () {
    var parseFn = String(parser.parse);
    if (!this.hasErrorRecovery) {
      parseFn = removeErrorRecovery(parseFn);
    }

    if (this.options['token-stack']) {
      parseFn = addTokenStack(parseFn);
    }

    // Generate code with fresh variable names
    nextVariableId = 0;
    var tableCode = this.generateTableCode(this.table);

    // Generate the initialization code
    var commonCode = tableCode.commonCode;

    // Generate the module creation code
    var moduleCode = "{";
    moduleCode += [
        "trace: " + String(this.trace || parser.trace),
        "yy: {}",
        "symbols_: " + JSON.stringify(this.symbols_),
        "terminals_: " + JSON.stringify(this.terminals_).replace(/"([0-9]+)":/g,"$1:"),
        "productions_: " + JSON.stringify(this.productions_),
        "performAction: " + String(this.performAction),
        "table: " + tableCode.moduleCode,
        "defaultActions: " + JSON.stringify(this.defaultActions).replace(/"([0-9]+)":/g,"$1:"),
        "parseError: " + String(this.parseError || (this.hasErrorRecovery ? traceParseError : parser.parseError)),
        "parse: " + parseFn
        ].join(",\n");
    moduleCode += "};";

    return { commonCode: commonCode, moduleCode: moduleCode }
};

// Generate code that represents the specified parser table
lrGeneratorMixin.generateTableCode = function (table) {
    var moduleCode = JSON.stringify(table);
    var variables = [createObjectCode];

    // Don't surround numerical property name numbers in quotes
    moduleCode = moduleCode.replace(/"([0-9]+)"(?=:)/g, "$1");

    // Replace objects with several identical values by function calls
    // e.g., { 1: [6, 7]; 3: [6, 7], 4: [6, 7], 5: 8 } = o([1, 3, 4], [6, 7], { 5: 8 })
    moduleCode = moduleCode.replace(/\{\d+:[^\}]+,\d+:[^\}]+\}/g, function (object) {
        // Find the value that occurs with the highest number of keys
        var value, frequentValue, key, keys = {}, keyCount, maxKeyCount = 0,
            keyValue, keyValues = [], keyValueMatcher = /(\d+):([^:]+)(?=,\d+:|\})/g;

        while ((keyValue = keyValueMatcher.exec(object))) {
            // For each value, store the keys where that value occurs
            key = keyValue[1];
            value = keyValue[2];
            keyCount = 1;

            if (!(value in keys)) {
                keys[value] = [key];
            } else {
                keyCount = keys[value].push(key);
            }
            // Remember this value if it is the most frequent one
            if (keyCount > maxKeyCount) {
                maxKeyCount = keyCount;
                frequentValue = value;
            }
        }
        // Construct the object with a function call if the most frequent value occurs multiple times
        if (maxKeyCount > 1) {
            // Collect all non-frequent values into a remainder object
            for (value in keys) {
                if (value !== frequentValue) {
                    for (var k = keys[value], i = 0, l = k.length; i < l; i++) {
                        keyValues.push(k[i] + ':' + value);
                    }
                }
            }
            keyValues = keyValues.length ? ',{' + keyValues.join(',') + '}' : '';
            // Create the function call `o(keys, value, remainder)`
            object = 'o([' + keys[frequentValue].join(',') + '],' + frequentValue + keyValues + ')';
        }
        return object;
    });

    // Count occurrences of number lists
    var list;
    var lists = {};
    var listMatcher = /\[[0-9,]+\]/g;

    while (list = listMatcher.exec(moduleCode)) {
        lists[list] = (lists[list] || 0) + 1;
    }

    // Replace frequently occurring number lists with variables
    moduleCode = moduleCode.replace(listMatcher, function (list) {
        var listId = lists[list];
        // If listId is a number, it represents the list's occurrence frequency
        if (typeof listId === 'number') {
            // If the list does not occur frequently, represent it by the list
            if (listId === 1) {
                lists[list] = listId = list;
            // If the list occurs frequently, represent it by a newly assigned variable
            } else {
                lists[list] = listId = createVariable();
                variables.push(listId + '=' + list);
            }
        }
        return listId;
    });

    // Return the variable initialization code and the table code
    return {
        commonCode: 'var ' + variables.join(',') + ';',
        moduleCode: moduleCode
    };
};
// Function that extends an object with the given value for all given keys
// e.g., o([1, 3, 4], [6, 7], { x: 1, y: 2 }) = { 1: [6, 7]; 3: [6, 7], 4: [6, 7], x: 1, y: 2 }
var createObjectCode = 'o=function(k,v,o,l){' +
    'for(o=o||{},l=k.length;l--;o[k[l]]=v);' +
    'return o}';

// Creates a variable with a unique name
function createVariable() {
    var id = nextVariableId++;
    var name = '$V';

    do {
        name += variableTokens[id % variableTokensLength];
        id = ~~(id / variableTokensLength);
    } while (id !== 0);

    return name;
}

var nextVariableId = 0;
var variableTokens = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$';
var variableTokensLength = variableTokens.length;

// default main method for generated commonjs modules
function commonjsMain (args) {
    if (!args[1]) {
        console.log('Usage: '+args[0]+' FILE');
        process.exit(1);
    }
    var source = require('fs').readFileSync(require('path').normalize(args[1]), "utf8");
    return exports.parser.parse(source);
}

// debug mixin for LR parser generators

function printAction (a, gen) {
    var s = a[0] == 1 ? 'shift token (then go to state '+a[1]+')' :
        a[0] == 2 ? 'reduce by rule: '+gen.productions[a[1]] :
                    'accept' ;

    return s;
}

var lrGeneratorDebug = {
    beforeparseTable: function () {
        this.trace("Building parse table.");
    },
    afterparseTable: function () {
        var self = this;
        if (this.conflicts > 0) {
            this.resolutions.forEach(function (r, i) {
                if (r[2].bydefault) {
                    self.warn('Conflict at state: ',r[0], ', token: ',r[1], "\n  ", printAction(r[2].r, self), "\n  ", printAction(r[2].s, self));
                }
            });
            this.trace("\n"+this.conflicts+" Conflict(s) found in grammar.");
        }
        this.trace("Done.");
    },
    aftercanonicalCollection: function (states) {
        var trace = this.trace;
        trace("\nItem sets\n------");

        states.forEach(function (state, i) {
            trace("\nitem set",i,"\n"+state.join("\n"), '\ntransitions -> ', JSON.stringify(state.edges));
        });
    }
};

var parser = typal.beget();

lrGeneratorMixin.createParser = function createParser () {

    var p = eval(this.generateModuleExpr());

    // for debugging
    p.productions = this.productions;

    var self = this;
    function bind(method) {
        return function() {
            self.lexer = p.lexer;
            return self[method].apply(self, arguments);
        };
    }

    // backwards compatability
    p.lexer = this.lexer;
    p.generate = bind('generate');
    p.generateAMDModule = bind('generateAMDModule');
    p.generateModule = bind('generateModule');
    p.generateCommonJSModule = bind('generateCommonJSModule');

    return p;
};

parser.trace = generator.trace;
parser.warn = generator.warn;
parser.error = generator.error;

function traceParseError (err, hash) {
    this.trace(err);
}

function parseError (str, hash) {
    if (hash.recoverable) {
        this.trace(str);
    } else {
        var error = new Error(str);
        error.hash = hash;
        throw error;
    }
}

parser.parseError = lrGeneratorMixin.parseError = parseError;

parser.parse = function parse (input) {
    var self = this,
        stack = [0],
        tstack = [], // token stack
        vstack = [null], // semantic value stack
        lstack = [], // location stack
        table = this.table,
        yytext = '',
        yylineno = 0,
        yyleng = 0,
        recovering = 0,
        TERROR = 2,
        EOF = 1;

    var args = lstack.slice.call(arguments, 1);

    //this.reductionCount = this.shiftCount = 0;

    var lexer = Object.create(this.lexer);
    var sharedState = { yy: {} };
    // copy state
    for (var k in this.yy) {
      if (Object.prototype.hasOwnProperty.call(this.yy, k)) {
        sharedState.yy[k] = this.yy[k];
      }
    }

    lexer.setInput(input, sharedState.yy);
    sharedState.yy.lexer = lexer;
    sharedState.yy.parser = this;
    if (typeof lexer.yylloc == 'undefined') {
        lexer.yylloc = {};
    }
    var yyloc = lexer.yylloc;
    lstack.push(yyloc);

    var ranges = lexer.options && lexer.options.ranges;

    if (typeof sharedState.yy.parseError === 'function') {
        this.parseError = sharedState.yy.parseError;
    } else {
        this.parseError = Object.getPrototypeOf(this).parseError;
    }

    function popStack (n) {
        stack.length = stack.length - 2 * n;
        vstack.length = vstack.length - n;
        lstack.length = lstack.length - n;
    }

_token_stack:
    var lex = function () {
        var token;
        token = lexer.lex() || EOF;
        // if token isn't its numeric value, convert
        if (typeof token !== 'number') {
            token = self.symbols_[token] || token;
        }
        return token;
    }

    var symbol, preErrorSymbol, state, action, a, r, yyval = {}, p, len, newState, expected;
    while (true) {
        // retreive state number from top of stack
        state = stack[stack.length - 1];

        // use default actions if available
        if (this.defaultActions[state]) {
            action = this.defaultActions[state];
        } else {
            if (symbol === null || typeof symbol == 'undefined') {
                symbol = lex();
            }
            // read action for current state and first input
            action = table[state] && table[state][symbol];
        }

_handle_error:
        // handle parse error
        if (typeof action === 'undefined' || !action.length || !action[0]) {
            var error_rule_depth;
            var errStr = '';

            // Return the rule stack depth where the nearest error rule can be found.
            // Return FALSE when no error recovery rule was found.
            function locateNearestErrorRecoveryRule(state) {
                var stack_probe = stack.length - 1;
                var depth = 0;

                // try to recover from error
                for(;;) {
                    // check for error recovery rule in this state
                    if ((TERROR.toString()) in table[state]) {
                        return depth;
                    }
                    if (state === 0 || stack_probe < 2) {
                        return false; // No suitable error recovery rule available.
                    }
                    stack_probe -= 2; // popStack(1): [symbol, action]
                    state = stack[stack_probe];
                    ++depth;
                }
            }

            if (!recovering) {
                // first see if there's any chance at hitting an error recovery rule:
                error_rule_depth = locateNearestErrorRecoveryRule(state);

                // Report error
                expected = [];
                for (p in table[state]) {
                    if (this.terminals_[p] && p > TERROR) {
                        expected.push("'"+this.terminals_[p]+"'");
                    }
                }
                if (lexer.showPosition) {
                    errStr = 'Parse error on line '+(yylineno+1)+":\n"+lexer.showPosition()+"\nExpecting "+expected.join(', ') + ", got '" + (this.terminals_[symbol] || symbol)+ "'";
                } else {
                    errStr = 'Parse error on line '+(yylineno+1)+": Unexpected " +
                                  (symbol == EOF ? "end of input" :
                                              ("'"+(this.terminals_[symbol] || symbol)+"'"));
                }
                this.parseError(errStr, {
                    text: lexer.match,
                    token: this.terminals_[symbol] || symbol,
                    line: lexer.yylineno,
                    loc: yyloc,
                    expected: expected,
                    recoverable: (error_rule_depth !== false)
                });
            } else if (preErrorSymbol !== EOF) {
                error_rule_depth = locateNearestErrorRecoveryRule(state);
            }

            // just recovered from another error
            if (recovering == 3) {
                if (symbol === EOF || preErrorSymbol === EOF) {
                    throw new Error(errStr || 'Parsing halted while starting to recover from another error.');
                }

                // discard current lookahead and grab another
                yyleng = lexer.yyleng;
                yytext = lexer.yytext;
                yylineno = lexer.yylineno;
                yyloc = lexer.yylloc;
                symbol = lex();
            }

            // try to recover from error
            if (error_rule_depth === false) {
                throw new Error(errStr || 'Parsing halted. No suitable error recovery rule available.');
            }
            popStack(error_rule_depth);

            preErrorSymbol = (symbol == TERROR ? null : symbol); // save the lookahead token
            symbol = TERROR;         // insert generic error symbol as new lookahead
            state = stack[stack.length-1];
            action = table[state] && table[state][TERROR];
            recovering = 3; // allow 3 real symbols to be shifted before reporting a new error
        }

        // this shouldn't happen, unless resolve defaults are off
        if (action[0] instanceof Array && action.length > 1) {
            throw new Error('Parse Error: multiple actions possible at state: '+state+', token: '+symbol);
        }

        switch (action[0]) {
            case 1: // shift
                //this.shiftCount++;

                stack.push(symbol);
                vstack.push(lexer.yytext);
                lstack.push(lexer.yylloc);
                stack.push(action[1]); // push state
                symbol = null;
                if (!preErrorSymbol) { // normal execution/no error
                    yyleng = lexer.yyleng;
                    yytext = lexer.yytext;
                    yylineno = lexer.yylineno;
                    yyloc = lexer.yylloc;
                    if (recovering > 0) {
                        recovering--;
                    }
                } else {
                    // error just occurred, resume old lookahead f/ before error
                    symbol = preErrorSymbol;
                    preErrorSymbol = null;
                }
                break;

            case 2:
                // reduce
                //this.reductionCount++;

                len = this.productions_[action[1]][1];

                // perform semantic action
                yyval.$ = vstack[vstack.length-len]; // default to $$ = $1
                // default location, uses first token for firsts, last for lasts
                yyval._$ = {
                    first_line: lstack[lstack.length-(len||1)].first_line,
                    last_line: lstack[lstack.length-1].last_line,
                    first_column: lstack[lstack.length-(len||1)].first_column,
                    last_column: lstack[lstack.length-1].last_column
                };
                if (ranges) {
                  yyval._$.range = [lstack[lstack.length-(len||1)].range[0], lstack[lstack.length-1].range[1]];
                }
                r = this.performAction.apply(yyval, [yytext, yyleng, yylineno, sharedState.yy, action[1], vstack, lstack].concat(args));

                if (typeof r !== 'undefined') {
                    return r;
                }

                // pop off stack
                if (len) {
                    stack = stack.slice(0,-1*len*2);
                    vstack = vstack.slice(0, -1*len);
                    lstack = lstack.slice(0, -1*len);
                }

                stack.push(this.productions_[action[1]][0]);    // push nonterminal (reduce)
                vstack.push(yyval.$);
                lstack.push(yyval._$);
                // goto new state = table[STATE][NONTERMINAL]
                newState = table[stack[stack.length-2]][stack[stack.length-1]];
                stack.push(newState);
                break;

            case 3:
                // accept
                return true;
        }

    }

    return true;
};

parser.init = function parser_init (dict) {
    this.table = dict.table;
    this.defaultActions = dict.defaultActions;
    this.performAction = dict.performAction;
    this.productions_ = dict.productions_;
    this.symbols_ = dict.symbols_;
    this.terminals_ = dict.terminals_;
};

/*
 * LR(0) Parser
 * */

var lr0 = generator.beget(lookaheadMixin, lrGeneratorMixin, {
    type: "LR(0)",
    afterconstructor: function lr0_afterconstructor () {
        this.buildTable();
    }
});

var LR0Generator = exports.LR0Generator = lr0.construct();

/*
 * Simple LALR(1)
 * */

var lalr = generator.beget(lookaheadMixin, lrGeneratorMixin, {
    type: "LALR(1)",

    afterconstructor: function (grammar, options) {
        if (this.DEBUG) this.mix(lrGeneratorDebug, lalrGeneratorDebug); // mixin debug methods

        options = options || {};
        this.states = this.canonicalCollection();
        this.terms_ = {};

        var newg = this.newg = typal.beget(lookaheadMixin,{
            oldg: this,
            trace: this.trace,
            nterms_: {},
            DEBUG: false,
            // FIXME: much optimization available here!!!
            go_: function (r, B) {
                r = r.split(":")[0]; // grab state #
                B = B.map(function (b) { return b.slice(b.indexOf(":")+1); });
                return this.oldg.go(r, B);
            }
        });
        newg.nonterminals = {};
        newg.productions = [];

        this.inadequateStates = [];

        // if true, only lookaheads in inadequate states are computed (faster, larger table)
        // if false, lookaheads for all reductions will be computed (slower, smaller table)
        this.onDemandLookahead = options.onDemandLookahead || false;

        this.buildNewGrammar();
        newg.computeLookaheads();
        this.unionLookaheads();

        this.table = this.parseTable(this.states);
        this.defaultActions = findDefaults(this.table);
    },

    lookAheads: function LALR_lookaheads (state, item) {
        return (!!this.onDemandLookahead && !state.inadequate) ? this.terminals : item.follows;
    },
    go: function LALR_go (p, w) {
        var q = parseInt(p, 10);
        for (var i=0;i<w.length;i++) {
            q = this.states.item(q).edges[w[i]] || q;
        }
        return q;
    },
    goPath: function LALR_goPath (p, w) {
        var q = parseInt(p, 10),t,
            path = [];
        for (var i=0;i<w.length;i++) {
            t = w[i] ? q+":"+w[i] : '';
            if (t) this.newg.nterms_[t] = q;
            path.push(t);
            q = this.states.item(q).edges[w[i]] || q;
            this.terms_[t] = w[i];
        }
        return {path: path, endState: q};
    },
    // every disjoint reduction of a nonterminal becomes a produciton in G'
    buildNewGrammar: function LALR_buildNewGrammar () {
        var self = this,
            newg = this.newg;

        // TODO: ???
        console.dir({ts22: this.states}, {depth: null});
        this.states.forEach((state, i) => {
            console.dir({ts: this.states, state});
            state.forEach((item) => {
                if (item.dotPosition === 0) {
                    // new symbols are a combination of state and transition symbol
                    var symbol = i+":"+item.production.symbol;
                    self.terms_[symbol] = item.production.symbol;
                    newg.nterms_[symbol] = i;
                    if (!newg.nonterminals[symbol])
                        newg.nonterminals[symbol] = new Nonterminal(symbol);
                    var pathInfo = self.goPath(i, item.production.handle);
                    var p = new Production(symbol, pathInfo.path, newg.productions.length);
                    newg.productions.push(p);
                    newg.nonterminals[symbol].productions.push(p);

                    // store the transition that get's 'backed up to' after reduction on path
                    var handle = item.production.handle.join(' ');
                    var goes = self.states.item(pathInfo.endState).goes;
                    if (!goes[handle])
                        goes[handle] = [];
                    goes[handle].push(symbol);

                    //self.trace('new production:',p);
                }
            });
            if (state.inadequate)
                self.inadequateStates.push(i);
        });
    },
    unionLookaheads: function LALR_unionLookaheads () {
        var self = this,
            newg = this.newg,
            states = !!this.onDemandLookahead ? this.inadequateStates : this.states;

        // console.dir({
        //     ts: this.states,
        //     ti: this.inadequateStates,
        //     to: this.onDemandLookahead,
        //     newg: this.newg,
        // });
        states.forEach(function union_states_forEach (i) {
            var state = typeof i === 'number' ? self.states.item(i) : i;
            // console.dir({
            //     s: Object.keys(state),
            //     r: state.reductions.slice(0, 4),
            //     l: state.reductions.length,
            //     i,
            // }, { depth: 3 });
            if (state.reductions.length)
            state.reductions.forEach(function union_reduction_forEach (item) {
                var follows = new Set([...item.follows]);
                // console.dir({item, follows, j: item.production.handle.join(' ')}, { depth: 3 });
                state.goes[item.production.handle.join(' ')].forEach(function reduction_goes_forEach (symbol) {
                    newg.nonterminals[symbol].follows.forEach(function goes_follows_forEach (symbol) {
                        var terminal = self.terms_[symbol];
                        if (!follows.has(terminal)) {
                            follows.add(terminal);
                            item.follows.push(terminal);
                        }
                    });
                });
                //self.trace('unioned item', item);
            });
        });
    }
});

var LALRGenerator = exports.LALRGenerator = lalr.construct();

// LALR generator debug mixin

var lalrGeneratorDebug = {
    trace: function trace () {
        Jison.print.apply(null, arguments);
    },
    beforebuildNewGrammar: function () {
        this.trace(this.states.size()+" states.");
        this.trace("Building lookahead grammar.");
    },
    beforeunionLookaheads: function () {
        this.trace("Computing lookaheads.");
    }
};

/*
 * Lookahead parser definitions
 *
 * Define base type
 * */
var lrLookaheadGenerator = generator.beget(lookaheadMixin, lrGeneratorMixin, {
    afterconstructor: function lr_aftercontructor () {
        this.computeLookaheads();
        this.buildTable();
    }
});

/*
 * SLR Parser
 * */
var SLRGenerator = exports.SLRGenerator = lrLookaheadGenerator.construct({
    type: "SLR(1)",

    lookAheads: function SLR_lookAhead (state, item) {
        return this.nonterminals[item.production.symbol].follows;
    }
});


/*
 * LR(1) Parser
 * */
var lr1 = lrLookaheadGenerator.beget({
    type: "Canonical LR(1)",

    lookAheads: function LR_lookAheads (state, item) {
        return item.follows;
    },
    Item: lrGeneratorMixin.Item.prototype.construct({
        afterconstructor: function () {
            this.id = this.production.id+'a'+this.dotPosition+'a'+this.follows.sort().join(',');
        },
        eq: function (e) {
            return e.id === this.id;
        }
    }),

    closureOperation: function LR_ClosureOperation (itemSet /*, closureSet*/) {
        var closureSet = new this.ItemSet();
        var self = this;

        var set = itemSet, itemQueue;

        do {
            itemQueue = new this.ItemSet();
            closureSet.concat(set);
            set.forEach(function (item) {
                var symbol = item.markedSymbol;
                var b, r;

                console.dir({item, rh: item.remainingHandle()});
                // if token is a nonterminal, recursively add closures
                if (symbol && self.nonterminals[symbol]) {
                    r = item.remainingHandle();
                    b = self.first(item.remainingHandle());
                    if (b.length === 0 || item.production.nullable || self.nullable(r)) {
                        b = b.concat(item.follows);
                    }
                    self.nonterminals[symbol].productions.forEach(function (production) {
                        var newItem = new self.Item(production, 0, b);
                        if(!closureSet.contains(newItem) && !itemQueue.contains(newItem)) {
                            itemQueue.push(newItem);
                        }
                    });
                } else if (!symbol) {
                    // reduction
                    closureSet.reductions.push(item);
                }
            });

            set = itemQueue;
        } while (!itemQueue.isEmpty());

        return closureSet;
    }
});

var LR1Generator = exports.LR1Generator = lr1.construct();

/*
 * LL Parser
 * */
var ll = generator.beget(lookaheadMixin, {
    type: "LL(1)",

    afterconstructor: function ll_aftercontructor () {
        this.computeLookaheads();
        this.table = this.parseTable(this.productions);
    },
    parseTable: function llParseTable (productions) {
        var table = {},
            self = this;
        productions.forEach(function (production, i) {
            var row = table[production.symbol] || {};
            var tokens = production.first;
            if (self.nullable(production.handle)) {
                SillySet.union(tokens, self.nonterminals[production.symbol].follows);
            }
            tokens.forEach(function (token) {
                if (row[token]) {
                    row[token].push(i);
                    self.conflicts++;
                } else {
                    row[token] = [i];
                }
            });
            table[production.symbol] = row;
        });

        return table;
    }
});

var LLGenerator = exports.LLGenerator = ll.construct();

Jison.Generator = function Jison_Generator (g, options) {
    var opt = typal.mix.call({}, g.options, options);
    switch (opt.type) {
        case 'lr0':
            return new LR0Generator(g, opt);
        case 'slr':
            return new SLRGenerator(g, opt);
        case 'lr':
            return new LR1Generator(g, opt);
        case 'll':
            return new LLGenerator(g, opt);
        default:
            return new LALRGenerator(g, opt);
    }
};

return function Parser (g, options) {
    var gen = Jison.Generator(g, options);
    return gen.createParser();
};

})();
