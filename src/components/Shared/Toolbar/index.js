import React, { Component } from "react"
import { Menu, Menubar, MenuItem, Divider } from "react-desktop-menus"
import { MdInsertDriveFile, MdFolder, MdSave, MdPrint, MdInput, MdHelp, MdUndo, MdRedo, MdSync, MdRefresh, MdAdd, MdLabel } from 'react-icons/md'

export default class Toolbar extends Component {
  dispatch = (fn) => () => {
    fn()
    this.menubar.close()
  }

  render() {
    const action = null
    return (
      <Menubar ref={ el => this.menubar = el } style={{ border : "1px solid #eee", zIndex: 1 }}>
        <Menu label="File">
          <MenuItem action={ action } icon={ <MdInsertDriveFile /> } label="New"/>
          <MenuItem action={this.dispatch(this.props.onOpen)} icon={ <MdFolder /> } label="Open"/>
          <Divider />
          <MenuItem action={ action } icon={ <MdSave /> } label="Save"/>
          <MenuItem action={this.dispatch(this.props.onSave)} label="Save As..."/>
          <Divider />
          <MenuItem action={ action } icon={ <MdLabel />} label="Lemmas" >
            <Menu>
              <MenuItem action={this.dispatch(this.props.onAddLemma)} label="Add a lemma"/>
              <MenuItem action={this.dispatch(this.props.onImportLemmas)} label="Import lemmas"/>
              <MenuItem action={this.dispatch(this.props.onExportLemmas)} label="Export lemmas"/>
            </Menu>
          </MenuItem>
          <Divider />
          <MenuItem action={ action } icon={ <MdPrint /> } label="Print"/>
          <MenuItem action={ action } icon={ <MdInput /> } label="Export">
            <Menu>
              <MenuItem action={this.dispatch(this.props.onExportPdf)} label="Export as PDF"/>
              <MenuItem action={ action } label="Export as PNG"/>
              <MenuItem action={ action } label="Export as TEX"/>
            </Menu>
          </MenuItem>
          <Divider />
          <MenuItem action={ action } label="Exit" />
        </Menu>
        <Menu label="Edit">
          <MenuItem action={this.dispatch(this.props.onUndo)} icon={ <MdUndo /> } label="Undo"/>
          <MenuItem action={this.dispatch(this.props.onRedo)} icon={ <MdRedo /> } label="Redo"/>
          <MenuItem action={this.dispatch(this.props.onClear)} icon={ <MdRefresh />} label="Clear"/>
          <MenuItem action={this.dispatch(this.props.onBeautify)} icon={ <MdSync />} label="Beautify" />
        </Menu>
        <Menu label="View">
          <MenuItem action={this.dispatch(this.props.onSwitch)} icon={ <MdSync /> } label={this.props.simple ? "Switch to Advanced Mode" : "Switch to Basic Mode"} />
        </Menu>
        <Menu label="Help">
          <MenuItem action={ action } icon={ <MdHelp /> } label="About iProve" />
        </Menu>
      </Menubar>
    )

  }

}
