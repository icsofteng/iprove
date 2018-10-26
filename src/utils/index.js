export const is_step = (step) =>
  Boolean(step) && step.ast && Object.keys(step.ast).length > 0 && step.dependencies