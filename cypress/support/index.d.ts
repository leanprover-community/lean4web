/// <reference types="cypress" />
/// <reference types="cypress-iframe" />

declare namespace Cypress {
  type Flatten<T> = T extends Iterable<infer Item> ? Item : never;
  type ArrayIterator<T, TResult> = (
    value: T,
    index: number,
    collection: T[],
  ) => TResult;
  type ContainsAllOptions = Partial<
    Loggable & Timeoutable & CaseMatchable & Shadow
  >;
  type ContainsAllFn = CommandFnWithSubject<
    "containsAll",
    void | JQueryWithSelector<HTMLElement>
  >;
  interface Chainable<Subject> {
    map<Item extends Flatten<Subject>, K extends keyof Item>(
      iteratee: K,
    ): Chainable<Item[K][]>;
    map<Item extends Flatten<Subject>, TResult>(
      iteratee: ArrayIterator<Item, TResult>,
    ): Chainable<TResult[]>;
    containsAll(
      contents: (string | number | RegExp)[],
      options?: ContainsAllOptions,
    ): Chainable<Subject>;
    containsAll<E extends Node = HTMLElement>(
      contents: (string | number | RegExp)[],
      options?: ContainsAllOptions,
    ): Chainable<JQuery<E>>;
    containsAll<K extends keyof HTMLElementTagNameMap>(
      selector: string,
      contents: (string | number | RegExp)[],
      options?: Partial<Loggable & Timeoutable & CaseMatchable>,
    ): Chainable<JQuery<HTMLElementTagNameMap[K]>>;
    containsAll<E extends Node = HTMLElement>(
      selector: string,
      contents: (string | number | RegExp)[],
      options?: Partial<Loggable & Timeoutable & CaseMatchable>,
    ): Chainable<JQuery<E>>;
  }
  interface Chainer<Subject> {
    (chainer: "be.open"): Chainable<Subject>;
    (chainer: "not.be.open"): Chainable<Subject>;
  }
}
