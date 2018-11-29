const is_subscope = (inner, outer) => outer.every(i => inner.indexOf(i) > -1)

export const findScope = (props, i) => {
  const steps = props[props.type]
  let s = steps[i]
  let findExit
  for (findExit = i; findExit < steps.length; findExit++) {
    if (!is_subscope(steps[findExit].scope, s.scope)) {
      break
    }
  }
  return findExit
}