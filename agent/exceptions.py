class FormalizerError(Exception):
    pass


class ParseError(FormalizerError):
    def __init__(self, message: str, partial_result=None):
        super().__init__(message)
        self.partial_result = partial_result


class GoalExtractionError(FormalizerError):
    pass


class GoalLockError(FormalizerError):
    pass


class GoalTamperedError(FormalizerError):
    """Unrecoverable — class F error. Never catch and retry."""
    pass


class BlueprintError(FormalizerError):
    pass


class PolibSaveError(FormalizerError):
    pass
