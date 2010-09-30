/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import java.awt.Color
import java.awt.Dimension
import java.awt.Rectangle

import java.util.HashMap
import java.util.Map

import javax.swing.JApplet
import javax.swing.JFrame

import org.jgrapht.ListenableGraph
import org.jgrapht.ext.JGraphModelAdapter
import org.jgrapht.graph.ListenableDirectedGraph
import org.jgrapht.graph.DefaultEdge

import org.jgraph.JGraph
import org.jgraph.graph.DefaultGraphCell
import org.jgraph.graph.GraphConstants
import org.jgraph.graph.AttributeMap

import com.mxgraph.swing.mxGraphComponent
import com.mxgraph.view.mxGraph

object GUI {

  class HypergraphVisualizer {
    val graph = new mxGraph();
    val parent = graph.getDefaultParent();

    graph.getModel().beginUpdate();
    val v1 = graph.insertVertex(parent, null, "Hello", 20, 20, 80,
                            30);
    val v2 = graph.insertVertex(parent, null, "World!", 240, 150,
                            80, 30);
    graph.insertEdge(parent, null, "Edge", v1, v2);
    graph.getModel().endUpdate();


    val graphComponent = new mxGraphComponent(graph);
    val frame = new JFrame();
    frame.getContentPane().add(graphComponent);
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    frame.setSize(400, 320);
    frame.setVisible(true);

    def test = {
      graph.insertVertex(parent, null, "Oi", 120, 60, 80,
                            30);
    }
  }


  class GraphVisualizer {
    private val DEFAULT_BG_COLOR = Color.decode( "#FAFBFF" );
    private val DEFAULT_SIZE = new Dimension( 530, 320 );

    val g : ListenableGraph[String,DefaultEdge] = new ListenableDirectedGraph( classOf[DefaultEdge] );
    private val m_jgAdapter = new JGraphModelAdapter( g )

    val jgraph = new JGraph( m_jgAdapter );

    val frame = new JFrame()
    adjustDisplaySettings( jgraph );
    frame.getContentPane(  ).add( jgraph );
    frame.resize( DEFAULT_SIZE );

    g.addVertex( "v1" );
    g.addVertex( "v2" );
    g.addVertex( "v3" );
    g.addVertex( "v4" );

    g.addEdge( "v1", "v2" );
    g.addEdge( "v2", "v3" );
    g.addEdge( "v3", "v1" );
    g.addEdge( "v4", "v3" );

    positionVertexAt( "v1", 130, 40 );
    positionVertexAt( "v2", 60, 200 );
    positionVertexAt( "v3", 310, 230 );
    positionVertexAt( "v4", 380, 70 );



    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
    frame.setVisible(true)


    private def adjustDisplaySettings(jg: JGraph) = {
        jg.setPreferredSize( DEFAULT_SIZE );
        val  c        = DEFAULT_BG_COLOR;
        var colorStr: String = null;
        jg.setBackground( c );
    }


    private def positionVertexAt( vertex:Object, x: Int, y:Int ) = {
      val cell : DefaultGraphCell = m_jgAdapter.getVertexCell( vertex );
  
      val attr: AttributeMap = cell.getAttributes(  );
      val b = GraphConstants.getBounds( attr ); // Rectangle
  
      GraphConstants.setBounds( attr, new Rectangle( x, y, b.getWidth.asInstanceOf[Int], b.getHeight.asInstanceOf[Int] ) );
  
      val cellAttr = new HashMap[DefaultGraphCell,AttributeMap]();
      cellAttr.put(cell, attr);
      m_jgAdapter.edit(cellAttr.asInstanceOf[Map[DefaultGraphCell,AttributeMap]], null, null, null);
    }
  }
}