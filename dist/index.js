function _interopDefault (ex) { return (ex && (typeof ex === 'object') && 'default' in ex) ? ex['default'] : ex; }

var React = _interopDefault(require('react'));

function _inheritsLoose(subClass, superClass) {
  subClass.prototype = Object.create(superClass.prototype);
  subClass.prototype.constructor = subClass;
  subClass.__proto__ = superClass;
}

function _assertThisInitialized(self) {
  if (self === void 0) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return self;
}

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

var reactIs_production_min = {
	AsyncMode: AsyncMode,
	ConcurrentMode: ConcurrentMode,
	ContextConsumer: ContextConsumer,
	ContextProvider: ContextProvider,
	Element: Element,
	ForwardRef: ForwardRef,
	Fragment: Fragment,
	Lazy: Lazy,
	Memo: Memo,
	Portal: Portal,
	Profiler: Profiler,
	StrictMode: StrictMode,
	Suspense: Suspense,
	isAsyncMode: isAsyncMode,
	isConcurrentMode: isConcurrentMode,
	isContextConsumer: isContextConsumer,
	isContextProvider: isContextProvider,
	isElement: isElement,
	isForwardRef: isForwardRef,
	isFragment: isFragment,
	isLazy: isLazy,
	isMemo: isMemo,
	isPortal: isPortal,
	isProfiler: isProfiler,
	isStrictMode: isStrictMode,
	isSuspense: isSuspense,
	isValidElementType: isValidElementType,
	typeOf: typeOf
};

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;
var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
// (unstable) APIs that have been removed. Can we remove the symbols?

var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
}

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;

    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;

          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;

              default:
                return $$typeof;
            }

        }

      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
} // AsyncMode is deprecated along with isAsyncMode

var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;
var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }

  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
exports.isValidElementType = isValidElementType;
exports.typeOf = typeOf;
  })();
}
});

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret;

var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has = Function.call.bind(Object.prototype.hasOwnProperty);

  printWarning = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes;

var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message) {
    this.message = message;
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning$1(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning$1(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning$1('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has$1(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning$1(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
          return null;
        }
      }

      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (!checker) {
          continue;
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from
      // props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

var propTypes = createCommonjsModule(function (module) {
/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = factoryWithThrowingShims();
}
});

function noop() {}
function returnTrue() {
  return true;
}
function charIsNumber(_char) {
  return !!(_char || '').match(/\d/);
}
function escapeRegExp(str) {
  return str.replace(/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g, "\\$&");
}
function fixLeadingZero(numStr) {
  if (!numStr) return numStr;
  var isNegative = numStr[0] === '-';
  if (isNegative) numStr = numStr.substring(1, numStr.length);
  var parts = numStr.split('.');
  var beforeDecimal = parts[0].replace(/^0+/, '') || '0';
  var afterDecimal = parts[1] || '';
  return "" + (isNegative ? '-' : '') + beforeDecimal + (afterDecimal ? "." + afterDecimal : '');
}
function splitString(str, index) {
  return [str.substring(0, index), str.substring(index)];
}
function limitToScale(numStr, scale, fixedDecimalScale) {
  var str = '';
  var filler = fixedDecimalScale ? '0' : '';

  for (var i = 0; i <= scale - 1; i++) {
    str += numStr[i] || filler;
  }

  return str;
}
function roundToPrecision(numStr, scale, fixedDecimalScale) {
  var numberParts = numStr.split('.');
  var roundedDecimalParts = parseFloat("0." + (numberParts[1] || '0')).toFixed(scale).split('.');
  var intPart = numberParts[0].split('').reverse().reduce(function (roundedStr, current, idx) {
    if (roundedStr.length > idx) {
      return (Number(roundedStr[0]) + Number(current)).toString() + roundedStr.substring(1, roundedStr.length);
    }

    return current + roundedStr;
  }, roundedDecimalParts[0]);
  var decimalPart = limitToScale(roundedDecimalParts[1] || '', (numberParts[1] || '').length, fixedDecimalScale);
  return intPart + (decimalPart ? '.' + decimalPart : '');
}
function omit(obj, keyMaps) {
  var filteredObj = {};
  Object.keys(obj).forEach(function (key) {
    if (!keyMaps[key]) filteredObj[key] = obj[key];
  });
  return filteredObj;
}
function setCaretPosition(el, caretPos) {
  el.value = el.value;

  if (el !== null) {
    if (el.createTextRange) {
      var range = el.createTextRange();
      range.move('character', caretPos);
      range.select();
      return true;
    }

    if (el.selectionStart || el.selectionStart === 0) {
      el.focus();
      el.setSelectionRange(caretPos, caretPos);
      return true;
    }

    el.focus();
    return false;
  }
}
var thousandGroupSpacing = {
  two: '2',
  twoScaled: '2s',
  three: '3',
  four: '4'
};

var propTypes$1 = {
  thousandSeparator: propTypes.oneOfType([propTypes.string, propTypes.oneOf([true])]),
  thousandSpacing: propTypes.oneOf(['2', '2s', '3', '4']),
  decimalSeparator: propTypes.string,
  decimalScale: propTypes.number,
  fixedDecimalScale: propTypes.bool,
  displayType: propTypes.oneOf(['input', 'text']),
  prefix: propTypes.string,
  suffix: propTypes.string,
  format: propTypes.oneOfType([propTypes.string, propTypes.func]),
  removeFormatting: propTypes.func,
  mask: propTypes.oneOfType([propTypes.string, propTypes.arrayOf(propTypes.string)]),
  value: propTypes.oneOfType([propTypes.number, propTypes.string]),
  isNumericString: propTypes.bool,
  customInput: propTypes.func,
  allowNegative: propTypes.bool,
  onValueChange: propTypes.func,
  onKeyDown: propTypes.func,
  onMouseUp: propTypes.func,
  onChange: propTypes.func,
  onFocus: propTypes.func,
  onBlur: propTypes.func,
  type: propTypes.oneOf(['text', 'tel']),
  isAllowed: propTypes.func,
  renderText: propTypes.func
};
var defaultProps = {
  displayType: 'input',
  decimalSeparator: '.',
  thousandSpacing: '3',
  fixedDecimalScale: false,
  prefix: '',
  suffix: '',
  allowNegative: true,
  isNumericString: false,
  type: 'text',
  onValueChange: noop,
  onChange: noop,
  onKeyDown: noop,
  onMouseUp: noop,
  onFocus: noop,
  onBlur: noop,
  isAllowed: returnTrue
};

var CurrencyFormat = /*#__PURE__*/function (_React$Component) {
  _inheritsLoose(CurrencyFormat, _React$Component);

  function CurrencyFormat(props) {
    var _this;

    _this = _React$Component.call(this, props) || this;

    _this.validateProps();

    var formattedValue = _this.formatValueProp();

    _this.state = {
      value: formattedValue,
      numAsString: _this.removeFormatting(formattedValue)
    };
    _this.onChange = _this.onChange.bind(_assertThisInitialized(_this));
    _this.onKeyDown = _this.onKeyDown.bind(_assertThisInitialized(_this));
    _this.onMouseUp = _this.onMouseUp.bind(_assertThisInitialized(_this));
    _this.onFocus = _this.onFocus.bind(_assertThisInitialized(_this));
    _this.onBlur = _this.onBlur.bind(_assertThisInitialized(_this));
    return _this;
  }

  var _proto = CurrencyFormat.prototype;

  _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
    this.updateValueIfRequired(prevProps);
  };

  _proto.updateValueIfRequired = function updateValueIfRequired(prevProps) {
    var props = this.props,
        state = this.state;

    if (prevProps !== props) {
      this.validateProps();
      var stateValue = state.value;
      var lastNumStr = state.numAsString || '';
      var formattedValue = props.value === undefined ? this.formatNumString(lastNumStr) : this.formatValueProp();

      if (formattedValue !== stateValue) {
        this.setState({
          value: formattedValue,
          numAsString: this.removeFormatting(formattedValue)
        });
      }
    }
  };

  _proto.getFloatString = function getFloatString(num) {
    if (num === void 0) {
      num = '';
    }

    var _this$getSeparators = this.getSeparators(),
        decimalSeparator = _this$getSeparators.decimalSeparator;

    var numRegex = this.getNumberRegex(true);
    var hasNegation = num[0] === '-';
    if (hasNegation) num = num.replace('-', '');
    num = (num.match(numRegex) || []).join('').replace(decimalSeparator, '.');
    var firstDecimalIndex = num.indexOf('.');

    if (firstDecimalIndex !== -1) {
      num = num.substring(0, firstDecimalIndex) + "." + num.substring(firstDecimalIndex + 1, num.length).replace(new RegExp(escapeRegExp(decimalSeparator), 'g'), '');
    }

    if (hasNegation) num = '-' + num;
    return num;
  };

  _proto.getNumberRegex = function getNumberRegex(g, ignoreDecimalSeparator) {
    var _this$props = this.props,
        format = _this$props.format,
        decimalScale = _this$props.decimalScale;

    var _this$getSeparators2 = this.getSeparators(),
        decimalSeparator = _this$getSeparators2.decimalSeparator;

    return new RegExp('\\d' + (decimalSeparator && decimalScale !== 0 && !ignoreDecimalSeparator && !format ? '|' + escapeRegExp(decimalSeparator) : ''), g ? 'g' : undefined);
  };

  _proto.getSeparators = function getSeparators() {
    var _this$props2 = this.props,
        decimalSeparator = _this$props2.decimalSeparator,
        thousandSpacing = _this$props2.thousandSpacing;
    var thousandSeparator = this.props.thousandSeparator;

    if (thousandSeparator === true) {
      thousandSeparator = ',';
    }

    return {
      decimalSeparator: decimalSeparator,
      thousandSeparator: thousandSeparator,
      thousandSpacing: thousandSpacing
    };
  };

  _proto.getMaskAtIndex = function getMaskAtIndex(index) {
    var _this$props$mask = this.props.mask,
        mask = _this$props$mask === void 0 ? ' ' : _this$props$mask;

    if (typeof mask === 'string') {
      return mask;
    }

    return mask[index] || ' ';
  };

  _proto.validateProps = function validateProps() {
    var mask = this.props.mask;

    var _this$getSeparators3 = this.getSeparators(),
        decimalSeparator = _this$getSeparators3.decimalSeparator,
        thousandSeparator = _this$getSeparators3.thousandSeparator;

    if (decimalSeparator === thousandSeparator) {
      throw new Error("\n          Decimal separator can't be same as thousand separator.\n\n          thousandSeparator: " + thousandSeparator + " (thousandSeparator = {true} is same as thousandSeparator = \",\")\n          decimalSeparator: " + decimalSeparator + " (default value for decimalSeparator is .)\n       ");
    }

    if (mask) {
      var maskAsStr = mask === 'string' ? mask : mask.toString();

      if (maskAsStr.match(/\d/g)) {
        throw new Error("\n          Mask " + mask + " should not contain numeric character;\n        ");
      }
    }
  };

  _proto.splitDecimal = function splitDecimal(numStr) {
    var allowNegative = this.props.allowNegative;
    var hasNagation = numStr[0] === '-';
    var addNegation = hasNagation && allowNegative;
    numStr = numStr.replace('-', '');
    var parts = numStr.split('.');
    var beforeDecimal = parts[0];
    var afterDecimal = parts[1] || '';
    return {
      beforeDecimal: beforeDecimal,
      afterDecimal: afterDecimal,
      hasNagation: hasNagation,
      addNegation: addNegation
    };
  };

  _proto.setPatchedCaretPosition = function setPatchedCaretPosition(el, caretPos, currentValue) {
    setCaretPosition(el, caretPos);
    setTimeout(function () {
      if (el.value === currentValue) setCaretPosition(el, caretPos);
    }, 0);
  };

  _proto.correctCaretPosition = function correctCaretPosition(value, caretPos, direction) {
    var _this$props3 = this.props,
        prefix = _this$props3.prefix,
        suffix = _this$props3.suffix,
        format = _this$props3.format;

    if (!format) {
      var hasNegation = value[0] === '-';
      return Math.min(Math.max(caretPos, prefix.length + (hasNegation ? 1 : 0)), value.length - suffix.length);
    }

    if (typeof format === 'function') return caretPos;
    if (format[caretPos] === '#' && charIsNumber(value[caretPos])) return caretPos;
    if (format[caretPos - 1] === '#' && charIsNumber(value[caretPos - 1])) return caretPos;
    var firstHashPosition = format.indexOf('#');
    var lastHashPosition = format.lastIndexOf('#');
    caretPos = Math.min(Math.max(caretPos, firstHashPosition), lastHashPosition + 1);
    var nextPos = format.substring(caretPos, format.length).indexOf('#');
    var caretLeftBound = caretPos;
    var caretRightBoud = caretPos + (nextPos === -1 ? 0 : nextPos);

    while (caretLeftBound > firstHashPosition && (format[caretLeftBound] !== '#' || !charIsNumber(value[caretLeftBound]))) {
      caretLeftBound -= 1;
    }

    var goToLeft = !charIsNumber(value[caretRightBoud]) || direction === 'left' && caretPos !== firstHashPosition || caretPos - caretLeftBound < caretRightBoud - caretPos;
    return goToLeft ? caretLeftBound + 1 : caretRightBoud;
  };

  _proto.getCaretPosition = function getCaretPosition(inputValue, formattedValue, caretPos) {
    var format = this.props.format;
    var stateValue = this.state.value;
    var numRegex = this.getNumberRegex(true);
    var inputNumber = (inputValue.match(numRegex) || []).join('');
    var formattedNumber = (formattedValue.match(numRegex) || []).join('');
    var j, i;
    j = 0;

    for (i = 0; i < caretPos; i++) {
      var currentInputChar = inputValue[i] || '';
      var currentFormatChar = formattedValue[j] || '';
      if (!currentInputChar.match(numRegex) && currentInputChar !== currentFormatChar) continue;
      if (currentInputChar === '0' && currentFormatChar.match(numRegex) && currentFormatChar !== '0' && inputNumber.length !== formattedNumber.length) continue;

      while (currentInputChar !== formattedValue[j] && j < formattedValue.length) {
        j++;
      }

      j++;
    }

    if (typeof format === 'string' && !stateValue) {
      j = formattedValue.length;
    }

    j = this.correctCaretPosition(formattedValue, j);
    return j;
  };

  _proto.removePrefixAndSuffix = function removePrefixAndSuffix(val) {
    var _this$props4 = this.props,
        format = _this$props4.format,
        prefix = _this$props4.prefix,
        suffix = _this$props4.suffix;

    if (!format && val) {
      var isNegative = val[0] === '-';
      if (isNegative) val = val.substring(1, val.length);
      val = prefix && val.indexOf(prefix) === 0 ? val.substring(prefix.length, val.length) : val;
      var suffixLastIndex = val.lastIndexOf(suffix);
      val = suffix && suffixLastIndex !== -1 && suffixLastIndex === val.length - suffix.length ? val.substring(0, suffixLastIndex) : val;
      if (isNegative) val = '-' + val;
    }

    return val;
  };

  _proto.removePatternFormatting = function removePatternFormatting(val) {
    var format = this.props.format;
    var formatArray = format.split('#').filter(function (str) {
      return str !== '';
    });
    var start = 0;
    var numStr = '';

    for (var i = 0, ln = formatArray.length; i <= ln; i++) {
      var part = formatArray[i] || '';
      var index = i === ln ? val.length : val.indexOf(part, start);

      if (index === -1) {
        numStr = val;
        break;
      } else {
        numStr += val.substring(start, index);
        start = index + part.length;
      }
    }

    return (numStr.match(/\d/g) || []).join('');
  };

  _proto.removeFormatting = function removeFormatting(val) {
    var _this$props5 = this.props,
        format = _this$props5.format,
        removeFormatting = _this$props5.removeFormatting;
    if (!val) return val;

    if (!format) {
      val = this.removePrefixAndSuffix(val);
      val = this.getFloatString(val);
    } else if (typeof format === 'string') {
      val = this.removePatternFormatting(val);
    } else if (typeof removeFormatting === 'function') {
      val = removeFormatting(val);
    } else {
      val = (val.match(/\d/g) || []).join('');
    }

    return val;
  };

  _proto.formatWithPattern = function formatWithPattern(numStr) {
    var format = this.props.format;
    var hashCount = 0;
    var formattedNumberAry = format.split('');

    for (var i = 0, ln = format.length; i < ln; i++) {
      if (format[i] === '#') {
        formattedNumberAry[i] = numStr[hashCount] || this.getMaskAtIndex(hashCount);
        hashCount += 1;
      }
    }

    return formattedNumberAry.join('');
  };

  _proto.formatThousand = function formatThousand(beforeDecimal, thousandSeparator, thousandSpacing) {
    var digitalGroup;

    switch (thousandSpacing) {
      case thousandGroupSpacing.two:
        digitalGroup = /(\d)(?=(\d{2})+(?!\d))/g;
        break;

      case thousandGroupSpacing.twoScaled:
        digitalGroup = /(\d)(?=(((\d{2})+)(\d{1})(?!\d)))/g;
        break;

      case thousandGroupSpacing.four:
        digitalGroup = /(\d)(?=(\d{4})+(?!\d))/g;
        break;

      default:
        digitalGroup = /(\d)(?=(\d{3})+(?!\d))/g;
    }

    return beforeDecimal.replace(digitalGroup, '$1' + thousandSeparator);
  };

  _proto.formatAsNumber = function formatAsNumber(numStr) {
    var _this$props6 = this.props,
        decimalScale = _this$props6.decimalScale,
        fixedDecimalScale = _this$props6.fixedDecimalScale,
        prefix = _this$props6.prefix,
        suffix = _this$props6.suffix;

    var _this$getSeparators4 = this.getSeparators(),
        thousandSeparator = _this$getSeparators4.thousandSeparator,
        decimalSeparator = _this$getSeparators4.decimalSeparator,
        thousandSpacing = _this$getSeparators4.thousandSpacing;

    var hasDecimalSeparator = numStr.indexOf('.') !== -1 || decimalScale && fixedDecimalScale;

    var _this$splitDecimal = this.splitDecimal(numStr),
        beforeDecimal = _this$splitDecimal.beforeDecimal,
        afterDecimal = _this$splitDecimal.afterDecimal,
        addNegation = _this$splitDecimal.addNegation;

    if (decimalScale !== undefined) afterDecimal = limitToScale(afterDecimal, decimalScale, fixedDecimalScale);

    if (thousandSeparator) {
      beforeDecimal = this.formatThousand(beforeDecimal, thousandSeparator, thousandSpacing);
    }

    if (prefix) beforeDecimal = prefix + beforeDecimal;
    if (suffix) afterDecimal = afterDecimal + suffix;
    if (addNegation) beforeDecimal = '-' + beforeDecimal;
    numStr = beforeDecimal + (hasDecimalSeparator && decimalSeparator || '') + afterDecimal;
    return numStr;
  };

  _proto.formatNumString = function formatNumString(value) {
    if (value === void 0) {
      value = '';
    }

    var format = this.props.format;
    var formattedValue = value;

    if (value === '') {
      formattedValue = '';
    } else if (value === '-' && !format) {
      formattedValue = '-';
      value = '';
    } else if (typeof format === 'string') {
      formattedValue = this.formatWithPattern(formattedValue);
    } else if (typeof format === 'function') {
      formattedValue = format(formattedValue);
    } else {
      formattedValue = this.formatAsNumber(formattedValue);
    }

    return formattedValue;
  };

  _proto.formatValueProp = function formatValueProp() {
    var _this$props7 = this.props,
        format = _this$props7.format,
        decimalScale = _this$props7.decimalScale,
        fixedDecimalScale = _this$props7.fixedDecimalScale;
    var _this$props8 = this.props,
        value = _this$props8.value,
        isNumericString = _this$props8.isNumericString;
    if (value === undefined) return '';

    if (typeof value === 'number') {
      value = value.toString();
      isNumericString = true;
    }

    if (isNumericString && !format && typeof decimalScale === 'number') {
      value = roundToPrecision(value, decimalScale, fixedDecimalScale);
    }

    var formattedValue = isNumericString ? this.formatNumString(value) : this.formatInput(value);
    return formattedValue;
  };

  _proto.formatNegation = function formatNegation(value) {
    if (value === void 0) {
      value = '';
    }

    var allowNegative = this.props.allowNegative;
    var negationRegex = new RegExp('(-)');
    var doubleNegationRegex = new RegExp('(-)(.)*(-)');
    var hasNegation = negationRegex.test(value);
    var removeNegation = doubleNegationRegex.test(value);
    value = value.replace(/-/g, '');

    if (hasNegation && !removeNegation && allowNegative) {
      value = '-' + value;
    }

    return value;
  };

  _proto.formatInput = function formatInput(value) {
    if (value === void 0) {
      value = '';
    }

    var format = this.props.format;

    if (!format) {
      value = this.formatNegation(value);
    }

    value = this.removeFormatting(value);
    return this.formatNumString(value);
  };

  _proto.isCharacterAFormat = function isCharacterAFormat(caretPos, value) {
    var _this$props9 = this.props,
        format = _this$props9.format,
        prefix = _this$props9.prefix,
        suffix = _this$props9.suffix,
        decimalScale = _this$props9.decimalScale,
        fixedDecimalScale = _this$props9.fixedDecimalScale;

    var _this$getSeparators5 = this.getSeparators(),
        decimalSeparator = _this$getSeparators5.decimalSeparator;

    if (typeof format === 'string' && format[caretPos] !== '#') return true;

    if (!format && (caretPos < prefix.length || caretPos >= value.length - suffix.length || decimalScale && fixedDecimalScale && value[caretPos] === decimalSeparator)) {
      return true;
    }

    return false;
  };

  _proto.checkIfFormatGotDeleted = function checkIfFormatGotDeleted(start, end, value) {
    for (var i = start; i < end; i++) {
      if (this.isCharacterAFormat(i, value)) return true;
    }

    return false;
  };

  _proto.correctInputValue = function correctInputValue(caretPos, lastValue, value) {
    var format = this.props.format;
    var lastNumStr = this.state.numAsString || '';

    if (value.length >= lastValue.length || !value.length) {
      return value;
    }

    var start = caretPos;
    var lastValueParts = splitString(lastValue, caretPos);
    var newValueParts = splitString(value, caretPos);
    var deletedIndex = lastValueParts[1].lastIndexOf(newValueParts[1]);
    var diff = deletedIndex !== -1 ? lastValueParts[1].substring(0, deletedIndex) : '';
    var end = start + diff.length;

    if (this.checkIfFormatGotDeleted(start, end, lastValue)) {
      value = lastValue;
    }

    if (!format) {
      var numericString = this.removeFormatting(value);

      var _this$splitDecimal2 = this.splitDecimal(numericString),
          beforeDecimal = _this$splitDecimal2.beforeDecimal,
          afterDecimal = _this$splitDecimal2.afterDecimal,
          addNegation = _this$splitDecimal2.addNegation;

      if (numericString.length < lastNumStr.length && beforeDecimal === '' && !parseFloat(afterDecimal)) {
        return addNegation ? '-' : '';
      }
    }

    return value;
  };

  _proto.onChange = function onChange(e) {
    e.persist();
    var el = e.target;
    var inputValue = el.value;
    var state = this.state,
        props = this.props;
    var isAllowed = props.isAllowed;
    var lastValue = state.value || '';
    var currentCaretPosition = Math.max(el.selectionStart, el.selectionEnd);
    inputValue = this.correctInputValue(currentCaretPosition, lastValue, inputValue);
    var formattedValue = this.formatInput(inputValue) || '';
    var numAsString = this.removeFormatting(formattedValue);
    var valueObj = {
      formattedValue: formattedValue,
      value: numAsString,
      floatValue: parseFloat(numAsString)
    };

    if (!isAllowed(valueObj)) {
      formattedValue = lastValue;
    }

    el.value = formattedValue;
    var caretPos = this.getCaretPosition(inputValue, formattedValue, currentCaretPosition);
    this.setPatchedCaretPosition(el, caretPos, formattedValue);

    if (formattedValue !== lastValue) {
      this.setState({
        value: formattedValue,
        numAsString: numAsString
      }, function () {
        props.onValueChange(valueObj);
        props.onChange(e);
      });
    } else {
      props.onChange(e);
    }
  };

  _proto.onBlur = function onBlur(e) {
    var props = this.props,
        state = this.state;
    var format = props.format,
        onBlur = props.onBlur;
    var numAsString = state.numAsString;
    var lastValue = state.value;

    if (!format) {
      numAsString = fixLeadingZero(numAsString);
      var formattedValue = this.formatNumString(numAsString);
      var valueObj = {
        formattedValue: formattedValue,
        value: numAsString,
        floatValue: parseFloat(numAsString)
      };

      if (formattedValue !== lastValue) {
        e.persist();
        this.setState({
          value: formattedValue,
          numAsString: numAsString
        }, function () {
          props.onValueChange(valueObj);
          onBlur(e);
        });
        return;
      }
    }

    onBlur(e);
  };

  _proto.onKeyDown = function onKeyDown(e) {
    var el = e.target;
    var key = e.key;
    var selectionEnd = el.selectionEnd,
        value = el.value;
    var selectionStart = el.selectionStart;
    var expectedCaretPosition;
    var _this$props10 = this.props,
        decimalScale = _this$props10.decimalScale,
        fixedDecimalScale = _this$props10.fixedDecimalScale,
        prefix = _this$props10.prefix,
        suffix = _this$props10.suffix,
        format = _this$props10.format,
        onKeyDown = _this$props10.onKeyDown;
    var ignoreDecimalSeparator = decimalScale !== undefined && fixedDecimalScale;
    var numRegex = this.getNumberRegex(false, ignoreDecimalSeparator);
    var negativeRegex = new RegExp('-');
    var isPatternFormat = typeof format === 'string';

    if (key === 'ArrowLeft' || key === 'Backspace') {
      expectedCaretPosition = selectionStart - 1;
    } else if (key === 'ArrowRight') {
      expectedCaretPosition = selectionStart + 1;
    } else if (key === 'Delete') {
      expectedCaretPosition = selectionStart;
    }

    if (expectedCaretPosition === undefined || selectionStart !== selectionEnd) {
      onKeyDown(e);
      return;
    }

    var newCaretPosition = expectedCaretPosition;
    var leftBound = isPatternFormat ? format.indexOf('#') : prefix.length;
    var rightBound = isPatternFormat ? format.lastIndexOf('#') + 1 : value.length - suffix.length;

    if (key === 'ArrowLeft' || key === 'ArrowRight') {
      var direction = key === 'ArrowLeft' ? 'left' : 'right';
      newCaretPosition = this.correctCaretPosition(value, expectedCaretPosition, direction);
    } else if (key === 'Delete' && !numRegex.test(value[expectedCaretPosition]) && !negativeRegex.test(value[expectedCaretPosition])) {
      while (!numRegex.test(value[newCaretPosition]) && newCaretPosition < rightBound) {
        newCaretPosition++;
      }
    } else if (key === 'Backspace' && !numRegex.test(value[expectedCaretPosition]) && !negativeRegex.test(value[expectedCaretPosition])) {
      while (!numRegex.test(value[newCaretPosition - 1]) && newCaretPosition > leftBound) {
        newCaretPosition--;
      }

      newCaretPosition = this.correctCaretPosition(value, newCaretPosition, 'left');
    }

    if (newCaretPosition !== expectedCaretPosition || expectedCaretPosition < leftBound || expectedCaretPosition > rightBound) {
      e.preventDefault();
      this.setPatchedCaretPosition(el, newCaretPosition, value);
    }

    if (e.isUnitTestRun) {
      this.setPatchedCaretPosition(el, newCaretPosition, value);
    }

    this.props.onKeyDown(e);
  };

  _proto.onMouseUp = function onMouseUp(e) {
    var el = e.target;
    var selectionStart = el.selectionStart,
        selectionEnd = el.selectionEnd,
        value = el.value;

    if (selectionStart === selectionEnd) {
      var caretPostion = this.correctCaretPosition(value, selectionStart);

      if (caretPostion !== selectionStart) {
        this.setPatchedCaretPosition(el, caretPostion, value);
      }
    }

    this.props.onMouseUp(e);
  };

  _proto.onFocus = function onFocus(e) {
    var _this2 = this;

    e.persist();
    setTimeout(function () {
      var el = e.target;
      var selectionStart = el.selectionStart,
          value = el.value;

      var caretPosition = _this2.correctCaretPosition(value, selectionStart);

      if (caretPosition !== selectionStart) {
        _this2.setPatchedCaretPosition(el, caretPosition, value);
      }

      _this2.props.onFocus(e);
    });
  };

  _proto.render = function render() {
    var _this$props11 = this.props,
        type = _this$props11.type,
        displayType = _this$props11.displayType,
        customInput = _this$props11.customInput,
        renderText = _this$props11.renderText;
    var value = this.state.value;
    var otherProps = omit(this.props, propTypes$1);
    var inputProps = Object.assign({}, otherProps, {
      type: type,
      value: value,
      onChange: this.onChange,
      onKeyDown: this.onKeyDown,
      onMouseUp: this.onMouseUp,
      onFocus: this.onFocus,
      onBlur: this.onBlur
    });

    if (displayType === 'text') {
      return renderText ? renderText(value) || null : /*#__PURE__*/React.createElement("span", otherProps, value);
    } else if (customInput) {
      var CustomInput = customInput;
      return /*#__PURE__*/React.createElement(CustomInput, inputProps);
    }

    return /*#__PURE__*/React.createElement("input", inputProps);
  };

  return CurrencyFormat;
}(React.Component);

CurrencyFormat.propTypes = propTypes$1;
CurrencyFormat.defaultProps = defaultProps;
module.exports = CurrencyFormat;
//# sourceMappingURL=index.js.map
