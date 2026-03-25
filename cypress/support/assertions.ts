chai.use(function (_chai, utils) {
  _chai.Assertion.addProperty("open", function () {
    const isOpen = utils.flag(this, "object").attr("open") != null;

    this.assert(
      isOpen,
      "expected #{this} to be open but it was not",
      "expected #{this} to not be open but it was",
      isOpen,
    );
  });
});
