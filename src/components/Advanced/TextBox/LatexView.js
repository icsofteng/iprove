import React from 'react'
import Latex from 'react-latex'
import { translate_rule as translate_latex } from '../../../translator/latex'
import styles from './styles.scss'

const LatexView = ({ onFocus, ast }) =>
  <div className={styles.latex} onClick={onFocus}>
    <Latex>{"$"+translate_latex(ast)+"$"}</Latex>
  </div>

export default LatexView