/*
 * Beautiful work from Justin Fagnani at https://justinfagnani.com/2015/12/21/real-mixins-with-javascript-classes/.
 * JS is a very slick and cool language sometimes...CoffeeScript is a fiery and spicy language at
 * all times.
 */

export let mix = (superclass) => new MixinBuilder(superclass);

export class MixinBuilder {
  constructor(superclass) {
    this.superclass = superclass;
  }

  with(...mixins) {
    return mixins.reduce((c, mixin) => mixin(c), this.superclass);
  }
}

if (typeof exports !== 'undefined') {
    exports.mix = mix;
    exports.MixinBuilder = MixinBuilder;
}
