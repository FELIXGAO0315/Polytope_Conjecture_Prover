class FormalizerError(Exception):
    pass


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
