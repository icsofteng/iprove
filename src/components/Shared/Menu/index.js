import React, { Component } from "react"
import { Menu, Menubar, MenuItem, Divider } from "react-desktop-menus"
import { MdInsertDriveFile, MdFolder, MdSave, MdPrint, MdInput, MdHelp, MdUndo, MdRedo, MdSync } from 'react-icons/md'

export default class MenuBar extends Component {
  onClick() {
    console.log("hello world")
    this.menubar.close()
  }

  render() {
    const action = this.onClick.bind(this)
    return (
      <Menubar ref={ elmt => this.menubar = elmt } style={ { border : "1px solid #eee" } } { ...this.props }>
        <Menu label="File">
          <MenuItem action={ action } icon={ <MdInsertDriveFile /> } label="New"/>
          <MenuItem action={ action } icon={ <MdFolder /> } label="Open"/>
          <Divider />
          <MenuItem action={ action } icon={ <MdSave /> } label="Save"/>
          <MenuItem action={ action } label="Save As..."/>
          <Divider />
          <MenuItem action={ action } icon={ <MdPrint /> } label="Print"/>
          <MenuItem action={ action } icon={ <MdInput /> } label="Export">
            <Menu>
              <MenuItem action={ action } label="Export as PDF"/>
              <MenuItem action={ action } label="Export as PNG"/>
              <MenuItem action={ action } label="Export as TEX"/>
            </Menu>
          </MenuItem>
          <Divider />
          <MenuItem action={ action } label="Exit" />
        </Menu>
        <Menu label="Edit">
          <MenuItem action={ action } icon={ <MdUndo /> } label="Undo"/>
          <MenuItem action={ action } icon={ <MdRedo /> } label="Redo"/>
        </Menu>
        <Menu label="View">
          <MenuItem action={ action } icon={ <MdSync /> } label="Switch to Basic Mode"/>
        </Menu>
        <Menu label="Help">
          <MenuItem action={ action } icon={ <MdHelp /> } label="About iProve" />
        </Menu>
      </Menubar>
    )

  }

}