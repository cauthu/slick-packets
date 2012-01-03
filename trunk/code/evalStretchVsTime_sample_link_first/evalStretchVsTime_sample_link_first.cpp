#include <boost/version.hpp>
#include <iostream>
#include <string>
#include <sstream>
#include <algorithm>
#include <iterator>
#include <fstream>
#include <memory>
#include <lemon/list_graph.h>
#include <lemon/dijkstra.h>
#include <lemon/concepts/graph.h>
#include <lemon/concepts/digraph.h>
#include <lemon/concepts/maps.h>
#include <lemon/random.h>
#include <map>
#include <set>
#include <assert.h>
#include <time.h>
#include <stdio.h>
#include <stdint.h>
#include <algorithm>
#include <stdexcept>
#include <boost/date_time.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/make_shared.hpp>
#include <boost/date_time/posix_time/posix_time.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/assign/list_of.hpp>
#include <sys/stat.h>
#include <sys/types.h>

static const char Id[] =
    "$Id$";

using namespace lemon;
using std::map;
using std::set;
using std::string;
using std::cout;
using std::endl;
using std::vector;
using std::min;
using std::max;
using std::ofstream;
using std::ostream;
using std::runtime_error;
using std::pair;
using std::make_pair;
using boost::shared_ptr;
using boost::make_shared;
using boost::posix_time::ptime;
using boost::assign::list_of;
using boost::assign::map_list_of;
using boost::make_tuple;
using boost::tuple;

typedef ListDigraph Graph_t;
typedef Graph_t::Arc Arc_t;
typedef Graph_t::Node Node_t;
// sometimes we need to represent an arc as a pair of node instead of
// Arc_t because as arcs are removed/added, the Arc_t might be changed
// underneath, as in, the arc's "id" might refer to a different arc.
typedef pair<Node_t, Node_t> NodePair_t;
// PathOfNodes_t is representation of a path as a list of nodes
// (instead of a list of arcs/edges). e.g., [s, a, b, c, t] means s
// and t are the source and the destination.
typedef vector<Node_t> PathOfNodes_t;
typedef Graph_t::ArcMap<double> WeightMap_t;
typedef Graph_t::NodeMap<double> DistMap_t;
typedef Path<Graph_t> Path_t;
typedef Dijkstra<Graph_t, WeightMap_t> Dijkstra_t;

typedef shared_ptr<vector<vector<double> > > (*calculatorFunc_t)(
        const PathOfNodes_t& ,
        const Node_t&,
        const double& ,
        const map<Node_t, map<Node_t, double> >& ,
        const double& ,
        const double& ,
        const double& ,
        const double& ,
        const double& );

#define ARRAY_LENGTH(array) (sizeof(array) / sizeof((array)[0]))

#define QUOTE(str) #str
#define EXPAND_AND_QUOTE(str) QUOTE(str)

template<typename T1, typename T2>
inline bool
inMap(const std::map<T1, T2>& m, const T1& k)
{
  return m.end() != m.find(k);
}

template<typename T1>
inline bool
inSet(const std::set<T1>& haystack, const T1& needle)
{
  return haystack.end() != haystack.find(needle);
}

static shared_ptr<PathOfNodes_t>
getPrefixNodes(const Graph_t& g, const Path_t& p,
                   const Node_t& stopNode=INVALID);

static const set<string> known_schemes = list_of
  ("SafeGuard")
  ("Fast-VSR")
  ("Fast-DAG")
  ("Flooded-DAG")
  ("Slow-DAG")
  ;

/* -------------------------------------------------------- */

/* remove BOTH the (u->v) and (v->u) arcs. return the weight attribute
 * of the (u->v) arc.
 */
static double
removeEdge(Graph_t& g, const Node_t& u, const Node_t& v,
           const WeightMap_t& weights)
{
    Arc_t a = findArc(g, u, v);
    double weight = weights[a];
    g.erase(a);
    Arc_t b = findArc(g, v, u);
    g.erase(b);
    return weight;
}

/* -------------------------------------------------------- */

/* add BOTH the (u->v) and (v->u) arcs. both arcs will get the
 * specified weight attribute.
 */
static void
addEdge(Graph_t& g, const Node_t& u, const Node_t& v,
        WeightMap_t& weights, const double& weight)
{
    Arc_t a = g.addArc(u, v);
    weights[a] = weight;
    Arc_t b = g.addArc(v, u);
    weights[b] = weight;
    return;
}

/* -------------------------------------------------------- */

static void
printPath(const Graph_t& g, const Path_t& path)
{
    cout << "path len (# of arcs): " << path.length() << endl;
    for (int i = 0; i < path.length(); ++i) {
        const Arc_t& a = path.nth(i);
        cout << "(" << g.id(g.source(a)) << ", " << g.id(g.target(a)) << "), ";
    }
    cout << endl;
    return;
}

/* -------------------------------------------------------- */

static void
printPathOfNodes(const Graph_t& g, const PathOfNodes_t& path)
{
    cout << "path of nodes [";
    for (PathOfNodes_t::const_iterator nit = path.begin();
         nit != path.end(); ++nit)
    {
        cout << g.id(*nit) << " ";
    }
    cout << "]";
    cout << endl;
    return;
}

/* -------------------------------------------------------- */

static void
load_graph(const char *filepath, Graph_t& g, bool weights,
           WeightMap_t& edge2Weights,
	   double* min_edge_weight, double* max_edge_weight)
{
    map<string, Node_t> name2Node;
    string line;
    std::ifstream file(filepath);

    if (file.is_open()) {
        while (file.good()) {
            getline(file, line);
	    std::istringstream iss(line);
            vector<string> tokens;
	    std::copy(std::istream_iterator<string>(iss),
		      std::istream_iterator<string>(),
		      std::back_inserter<vector<string> >(tokens));
            if (tokens.size() == 0) {
                continue;
            }
            string& uName = tokens[0];
            string& vName = tokens[1];
            Node_t uNode, vNode;

            map<string, Node_t>::iterator it;

            it = name2Node.find(uName);
            if (it != name2Node.end()) {
                uNode = it->second;
            }
            else {
                uNode = g.addNode();
                name2Node[uName] = uNode;
            }

            it = name2Node.find(vName);
            if (it != name2Node.end()) {
                vNode = it->second;
            }
            else {
                vNode = g.addNode();
                name2Node[vName] = vNode;
            }

            Arc_t a = g.addArc(uNode, vNode);
            double w = 1;
            if (weights == true) {
                assert (tokens.size() == 3);
                w = atof(tokens[2].c_str());
		if (min_edge_weight) {
		  *min_edge_weight = std::min(w, *min_edge_weight);
		}
		if (max_edge_weight) {
		  *max_edge_weight = std::max(w, *max_edge_weight);
		}
            }
            edge2Weights.set(a, w);
        }
    }
}

/* -------------------------------------------------------- */

static bool
isArcInPath(const Arc_t& a, const Path_t& p)
{
    for (Path_t::ArcIt ait(p); ait != INVALID; ++ait) {
        if (a == ait) {
            return true;
        }
    }
    return false;
}

/* -------------------------------------------------------- */

static shared_ptr<vector<shared_ptr<PathOfNodes_t> > >
getPathsThatUseEdge(const Graph_t& g, const WeightMap_t& weights,
                    const Node_t& src, const Arc_t& arc,
                    const int dstsamplesize=-1, Random* dstrandomObj=NULL)
{
    Dijkstra_t dijk(g, weights);
    dijk.init();
    dijk.addSource(src);
    dijk.start();
    const Node_t& u = g.source(arc);
    const Node_t& v = g.target(arc);
    const Arc_t& reverse_arc = findArc(g, v, u);
    // gather all the paths that use this edge, EITHER u->v or v->u.
    shared_ptr<vector<shared_ptr<PathOfNodes_t> > > paths = 
        make_shared<vector<shared_ptr<PathOfNodes_t> > >();
    for (Graph_t::NodeIt nit(g); nit != INVALID; ++nit) {
        if (nit == src) {
            continue;
        }
        const Path_t& p = dijk.path(nit);
        if (isArcInPath(arc, p) || isArcInPath(reverse_arc, p)) {
            shared_ptr<PathOfNodes_t> pathofnodes = getPrefixNodes(g, p);
            paths->push_back(pathofnodes);
        }
    }
    if (dstsamplesize > 0 && paths->size() > dstsamplesize) {
        assert (dstrandomObj != NULL);
        // only return dstsamplesize number of paths, so remove
        // (paths->size() - dstsamplesize) number of paths.
        const int numToRemove = paths->size() - dstsamplesize;
        for (int i = 0; i < numToRemove; ++i) {
            paths->erase(paths->begin() + dstrandomObj->integer(paths->size()));
        }
    }
    return paths;
}

/* -------------------------------------------------------- */
#if 0
static shared_ptr<map<NodePair_t, shared_ptr<vector<shared_ptr<PathOfNodes_t> > > > >
getEdgesAndPaths(const Graph_t& g, const WeightMap_t& weights, const Node_t& src,
                 const int edgeSampleSize, Random& edgerandomObj,
                 const int dstSampleSize, Random& dstrandomObj)
{
    Dijkstra_t dijk(g, weights);
    dijk.init();
    dijk.addSource(src);
    dijk.start();
    // gather all the paths and all edges used in those paths
    set<Arc_t> allEdgesSet;
    // "- 1" because we will skip the src
    vector<Path_t> allPaths(countNodes<>(g) - 1);
    int i = 0;
    for (Graph_t::NodeIt nit(g); nit != INVALID; ++nit) {
        if (nit == src) {
            continue;
        }
        const Path_t& p = dijk.path(nit);
        // DO NOT use push_back() because we've already allocated the space
        allPaths[i] = p;
        i++;
        for (Path_t::ArcIt ait(p); ait != INVALID; ++ait) {
            allEdgesSet.insert(ait);
        }
    }
    // need the edges in vector so we can get random index
    vector<Arc_t> allEdgesVec(allEdgesSet.size());
    copy(allEdgesSet.begin(), allEdgesSet.end(), allEdgesVec.begin());
    // sample the edges
    set<Arc_t> edges;
    int maxNumTries = edgeSampleSize * 3;
    int numTries = 0;
    while ((edges.size() < edgeSampleSize) && (numTries++ < maxNumTries)) {
        int idx = edgerandomObj.integer(allEdgesVec.size());
        const Arc_t& a = allEdgesVec[idx];
        edges.insert(a);
    }
    // for each edge, sample the paths that use it
    shared_ptr<map<NodePair_t, shared_ptr<vector<shared_ptr<PathOfNodes_t> > > > > edge2PathsThatUseEdge =
        make_shared<map<NodePair_t, shared_ptr<vector<shared_ptr<PathOfNodes_t> > > > >();
    for (set<Arc_t>::const_iterator ait = edges.begin();
         ait != edges.end(); ++ait)
    {
        const Arc_t& arc = *ait;
        shared_ptr<vector<shared_ptr<PathOfNodes_t> > > pathsThatUseEdge = make_shared<vector<shared_ptr<PathOfNodes_t> > >();
        for (vector<Path_t>::const_iterator pit = allPaths.begin();
             pit != allPaths.end(); ++pit)
        {
            const Path_t& path = *pit;
            if (isArcInPath(arc, path)) {
                shared_ptr<PathOfNodes_t> pon = getPrefixNodes(g, path);
                pathsThatUseEdge->push_back(pon);
            }
        }
        edge2PathsThatUseEdge->insert(
            make_pair(
                make_pair(g.source(arc), g.target(arc)),
                pathsThatUseEdge));
    }
    return edge2PathsThatUseEdge;
}
#endif
/* -------------------------------------------------------- */

// convert a Path_t to a PathOfNodes_t. if "stopNode" is specified and
// is an actual node in the path, then the returned PathOfNodes_t will
// end at "stopNode", inclusive. otherwise, all nodes in the path will
// be in the returned value.

static shared_ptr<PathOfNodes_t>
getPrefixNodes(const Graph_t& g, const Path_t& p,
               const Node_t& stopNode)
{
    shared_ptr<PathOfNodes_t> pathnodes = make_shared<PathOfNodes_t>();
    for (PathNodeIt<Path_t> pnit(g, p); pnit != INVALID; ++pnit) {
        pathnodes->push_back(pnit);
        if (stopNode == pnit) {
            break;
        }
    }
    return pathnodes;
}

/* -------------------------------------------------------- */

static shared_ptr<vector<vector<double> > >
calculateForSafeGuard(const PathOfNodes_t& shortestPath,
                      const Node_t& fn1,
                      const double& shortestLengthWithFailure,
                      const map<Node_t, map<Node_t, double> >& preCalculatedPathLengthsDict,
                      const double& spfDelay,
                      const double& spfComputeTime,
                      const double& fibUpdateTime,
                      const double& passThruDelay,
                      const double& timeOfFailure)
{
    shared_ptr<vector<vector<double> > > packetSentTime2Stretch =
        make_shared<vector<vector<double> > >();

    const Node_t& s = shortestPath[0];
    const Node_t& d = shortestPath.back();
    const PathOfNodes_t& shortestPathWithNoFailure = shortestPath;

    const double updatedelays = spfDelay + spfComputeTime + fibUpdateTime;

#if DEBUG
    printPathOfNodes(g, shortestPath);
#endif

    const int fn1Idx = find(shortestPathWithNoFailure.begin(), 
                            shortestPathWithNoFailure.end(), fn1)
                       -
                       shortestPathWithNoFailure.begin();
    for (int j = fn1Idx; j > -1; --j) {
        const Node_t& r = shortestPathWithNoFailure[j];

        const map<Node_t, double>& ssspl_r = preCalculatedPathLengthsDict.at(r);
        double t_tx;
        double stretch;
        if (j == fn1Idx) {
            /* with precomputed alternate paths, r_0 can immediately
             * start rerouting packets without incurring any delay
             */
            t_tx = max(0.0,
                       timeOfFailure - ssspl_r.at(s));
            // its stretch
            stretch = (ssspl_r.at(s) + ssspl_r.at(d)) / 
                shortestLengthWithFailure;
            assert (packetSentTime2Stretch->size() == 0);
            packetSentTime2Stretch->push_back(list_of(t_tx)(stretch));
#if 0
            if (processingDelay > 0) {
                // sent time of the first packet that will arrive at
                // r_0 right when it's finished computing new SPT and
                // updating FIB, etc... ie, this packet will not have
                // to be buffered.
                t_tx = max(0.0,
                           timeOfFailure + processingDelay - ssspl_r.at(s));
                // its stretch
                stretch = (double)(ssspl_r.at(s) + ssspl_r.at(d)) / shortestLengthWithFailure;
                if (packetSentTime2Stretch->back()[0] == t_tx) {
                    // the last t_tx is the same as our t_tx
                    assert (t_tx == 0 && packetSentTime2Stretch->size() == 1);
                    // instead of appending, we should replace
                    (*packetSentTime2Stretch)[0] = list_of(t_tx)(stretch);
                }
                else {
                    packetSentTime2Stretch->push_back(list_of(t_tx)(stretch));
                    double start = (floor((*packetSentTime2Stretch)[0][0])) + 1;
                    if (start >= t_tx) {
                        continue;
                    }
                    double start_stretch = packetSentTime2Stretch->back()[1] +
                                    ((packetSentTime2Stretch->back()[0] - start) /
                                     shortestLengthWithFailure);
                    double stop = int(ceil((*packetSentTime2Stretch)[1][0])) - 1;
                    if (start < stop) {
                        double stop_stretch = packetSentTime2Stretch->back()[1] +
                                       ((packetSentTime2Stretch->back()[0] - stop) /
                                        shortestLengthWithFailure);
                        packetSentTime2Stretch->insert(
                            packetSentTime2Stretch->end()-1,
                            list_of(start)(start_stretch)(stop)(stop_stretch));
                    }
                    else {
                        packetSentTime2Stretch->insert(
                            packetSentTime2Stretch->end()-1,
                            list_of(start)(start_stretch));
                    }
                }
            }
#endif
            // we have handled special case of r_0, do a "continue"
            continue;
        }
        else {
            stretch = (ssspl_r.at(s) + ssspl_r.at(d)) / shortestLengthWithFailure;
	    // "max(0, (fn1Idx - j) - 1)" to count only intermediate hops
            t_tx = max(0.0,
                       timeOfFailure + ssspl_r.at(fn1) +
                       max(0, (fn1Idx - j) - 1)*passThruDelay +
                       updatedelays - ssspl_r.at(s));
        }
        
        // append to or or update result
        if (packetSentTime2Stretch->size() == 0) {
            packetSentTime2Stretch->push_back(list_of(t_tx)(stretch));
        }
        else {
            assert (t_tx >= packetSentTime2Stretch->back()[0]);
            if (packetSentTime2Stretch->back()[0] == t_tx) {
                //  the last t_tx is the same
                assert (t_tx == 0 && packetSentTime2Stretch->size() == 1);
                // instead of appending, we should replace
                (*packetSentTime2Stretch)[0] = list_of(t_tx)(stretch);
            }
            else {
                // only need to add if it's different than the stretch
                // at the back of the array.
                if (stretch != packetSentTime2Stretch->back().back()) {
                    packetSentTime2Stretch->push_back(list_of(t_tx)(stretch));
                }
            }
        }
        
        if (stretch == 1) {
            break;
        }
    }
    
    if ((*packetSentTime2Stretch)[0][0] > 0) {
        packetSentTime2Stretch->insert(
            packetSentTime2Stretch->begin(), list_of(0)(1));
    }
    if (packetSentTime2Stretch->back()[1] != 1) {
        throw runtime_error("the last stretch must be 1.");
    }

    return packetSentTime2Stretch;
}

/* -------------------------------------------------------- */

enum scr_mode_t {
    FLOODED,
    FAST,
    SLOW,
} ;

static shared_ptr<vector<vector<double> > >
calculateForDAG(  const PathOfNodes_t& shortestPath,
                      const Node_t& fn1,
                      const double& shortestLengthWithFailure,
                      const map<Node_t, map<Node_t, double> >& preCalculatedPathLengthsDict,
                      const scr_mode_t& mode,
                      const double& spfDelay,
                      const double& spfComputeTime,
                      const double& fibUpdateTime,
                      const double& passThruDelay,
                      const double& timeOfFailure)
{
    shared_ptr<vector<vector<double> > > packetSentTime2Stretch =
        make_shared<vector<vector<double> > >();

    const Node_t& s = shortestPath[0];
    const Node_t& d = shortestPath.back();
//    const PathOfNodes_t& shortestPathWithNoFailure = shortestPath;

    const double updatedelays = spfDelay + spfComputeTime + fibUpdateTime;

    double distFromSToFn1 = preCalculatedPathLengthsDict.at(fn1).at(s);
    double distFromFn1ToD = preCalculatedPathLengthsDict.at(fn1).at(d);
    double takenPathLen = distFromSToFn1 + distFromFn1ToD;

    double     stretch = (takenPathLen)/shortestLengthWithFailure;

    double    t_tx = max(0.0, timeOfFailure - distFromSToFn1);
    packetSentTime2Stretch->push_back(list_of(t_tx)( stretch));
    if (stretch != 1) {
        double sourceUpdatedTime ;
        if (mode == FLOODED) {
            int fn1Idx = find(shortestPath.begin(), 
                                        shortestPath.end(), fn1)
                                        -
                                   shortestPath.begin();
	    // "max(0, (fn1Idx - 1))" to count only intermediate hops
            sourceUpdatedTime = timeOfFailure + 
                                distFromSToFn1 + 
	                        max(0, fn1Idx - 1)*passThruDelay + 
	                        updatedelays;
        }
        else if (mode == FAST) {
            sourceUpdatedTime = max(timeOfFailure, distFromSToFn1) + 
                                distFromSToFn1 + 
                                updatedelays;
        }
        else if (mode == SLOW) {
            sourceUpdatedTime = max(timeOfFailure, distFromSToFn1) + 
                                distFromFn1ToD + 
                                shortestLengthWithFailure + 
                                updatedelays;
        }
        else {
            throw runtime_error("invalid mode ");
        }
        packetSentTime2Stretch->push_back(list_of(sourceUpdatedTime)( 1));
    }

    if ((*packetSentTime2Stretch)[0][0] > 0) {
        packetSentTime2Stretch->insert(packetSentTime2Stretch->begin(),
                                       list_of(0)( 1));
    }
    if ((*packetSentTime2Stretch).back()[1] != 1) {
        throw runtime_error("the last stretch must be 1");
    }

    return packetSentTime2Stretch;
}

/* -------------------------------------------------------- */

static shared_ptr<vector<vector<double> > >
calculateForFastDAG_wrapper(  const PathOfNodes_t& shortestPath,
                      const Node_t& fn1,
                      const double& shortestLengthWithFailure,
                      const map<Node_t, map<Node_t, double> >& preCalculatedPathLengthsDict,
                      const double& spfDelay,
                      const double& spfComputeTime,
                      const double& fibUpdateTime,
                      const double& passThruDelay,
                      const double& timeOfFailure)
{
    return calculateForDAG(
        shortestPath, fn1, shortestLengthWithFailure,
        preCalculatedPathLengthsDict, FAST,
        spfDelay, spfComputeTime, fibUpdateTime, passThruDelay, timeOfFailure);
}

/* -------------------------------------------------------- */

static shared_ptr<vector<vector<double> > >
calculateForSlowDAG_wrapper(  const PathOfNodes_t& shortestPath,
                      const Node_t& fn1,
                      const double& shortestLengthWithFailure,
                      const map<Node_t, map<Node_t, double> >& preCalculatedPathLengthsDict,
                      const double& spfDelay,
                      const double& spfComputeTime,
                      const double& fibUpdateTime,
                      const double& passThruDelay,
                      const double& timeOfFailure)
{
    return calculateForDAG(
        shortestPath, fn1, shortestLengthWithFailure,
        preCalculatedPathLengthsDict, SLOW,
        spfDelay, spfComputeTime, fibUpdateTime, passThruDelay, timeOfFailure);
}

/* -------------------------------------------------------- */

static shared_ptr<vector<vector<double> > >
calculateForFloodedDAG_wrapper(  const PathOfNodes_t& shortestPath,
                      const Node_t& fn1,
                      const double& shortestLengthWithFailure,
                      const map<Node_t, map<Node_t, double> >& preCalculatedPathLengthsDict,
                      const double& spfDelay,
                      const double& spfComputeTime,
                      const double& fibUpdateTime,
                      const double& passThruDelay,
                      const double& timeOfFailure)
{
    return calculateForDAG(
        shortestPath, fn1, shortestLengthWithFailure,
        preCalculatedPathLengthsDict, FLOODED,
        spfDelay, spfComputeTime, fibUpdateTime, passThruDelay, timeOfFailure);
}

/* -------------------------------------------------------- */

static shared_ptr<vector<vector<double> > >
calculateForFastVSR(  const PathOfNodes_t& shortestPath,
                      const Node_t& fn1,
                      const double& shortestLengthWithFailure,
                      const map<Node_t, map<Node_t, double> >& preCalculatedPathLengthsDict,
                      const double& spfDelay,
                      const double& spfComputeTime,
                      const double& fibUpdateTime,
                      const double& passThruDelay,
                      const double& timeOfFailure)
{
    shared_ptr<vector<vector<double> > > packetSentTime2Stretch =
        make_shared<vector<vector<double> > >();

    const Node_t& s = shortestPath[0];
//    const Node_t& d = shortestPath.back();
//    const PathOfNodes_t& shortestPathWithNoFailure = shortestPath;

    const double updatedelays = spfDelay + spfComputeTime + fibUpdateTime;
    
    if (s == fn1 && updatedelays == 0) {
       (*packetSentTime2Stretch).push_back(list_of(min(0.0, timeOfFailure))(1));
       return packetSentTime2Stretch;
    }
    double distFromSToFn1 = preCalculatedPathLengthsDict.at(fn1).at(s);
//    double distFromFn1ToD = preCalculatedPathLengthsDict.at(fn1).at(d);
    double t_tx_converged;
    if (s != fn1) {
        double t_tx_firstResent = max(0.0, timeOfFailure - distFromSToFn1);
        double stretch_firstResent = 
	  ((2*distFromSToFn1) + updatedelays + shortestLengthWithFailure) / shortestLengthWithFailure;
        packetSentTime2Stretch->push_back(list_of(t_tx_firstResent)(stretch_firstResent));

        double t_tx_lastResent = t_tx_firstResent + (2*distFromSToFn1);
        
        double start = floor(t_tx_firstResent) + 1;
        double start_stretch = stretch_firstResent - 
                        ((start - t_tx_firstResent) / 
                         shortestLengthWithFailure);
        double stop = (ceil(t_tx_lastResent)) - 1;
        if (start < stop) {
            double stop_stretch = stretch_firstResent - 
                           ((stop - t_tx_firstResent) / 
                            shortestLengthWithFailure);
            packetSentTime2Stretch->push_back(
                list_of(start)(start_stretch)(stop)( stop_stretch));
        }
        else {
            packetSentTime2Stretch->push_back(
                list_of(start)( start_stretch));
        }

        t_tx_converged = t_tx_lastResent;
    }
    
    if (updatedelays > 0) {
        double t_tx_firstDelayed = max(0.0, timeOfFailure - distFromSToFn1) + 
                            (2*distFromSToFn1);
        double stretch_firstDelayed = ((updatedelays) + shortestLengthWithFailure) / shortestLengthWithFailure;
        packetSentTime2Stretch->push_back(list_of(t_tx_firstDelayed)( stretch_firstDelayed));

        double t_tx_lastDelayed = t_tx_firstDelayed + updatedelays;
     
        double start = (t_tx_firstDelayed) + 1;
        double start_stretch = stretch_firstDelayed - 
                      ((start - t_tx_firstDelayed) / 
                       shortestLengthWithFailure);
        double stop = (ceil(t_tx_lastDelayed)) - 1;
        if (start < stop) {
            double stop_stretch = stretch_firstDelayed - 
                           ((stop - t_tx_firstDelayed) / 
                            shortestLengthWithFailure);
            packetSentTime2Stretch->push_back(
                list_of(start)( start_stretch)( stop)( stop_stretch));
        }
        else {
            packetSentTime2Stretch->push_back(
                list_of(start)( start_stretch));
        }
        t_tx_converged = t_tx_lastDelayed;
    }

    packetSentTime2Stretch->push_back(list_of(t_tx_converged)( 1));

    if ((*packetSentTime2Stretch)[0][0] > 0) {
        packetSentTime2Stretch->insert(packetSentTime2Stretch->begin(),
                                       list_of(0)( 1));
    }
    if (packetSentTime2Stretch->back()[1] != 1) {
        throw runtime_error("the last stretch must be 1, shortestPath [%s]");
    }

    return packetSentTime2Stretch;
}

/* -------------------------------------------------------- */

static void
outputTime2Stretch(ostream& outputstream,
                   const vector<vector<double> >& time2Stretch_vec)
{
    for (vector<vector<double> >::const_iterator it = time2Stretch_vec.begin();
         it != time2Stretch_vec.end(); ++it)
    {
        const vector<double>& time2Stretch = *it;
        for (int i = 0; i < time2Stretch.size(); ++i) {
            outputstream << time2Stretch[i];
            if (i < (time2Stretch.size() - 1)) {
                outputstream << ",";
            }
        }
        if (it < (time2Stretch_vec.end() - 1)) {
            outputstream << "|";
        }
    }
    outputstream << endl;
    return;
}

static shared_ptr<vector<pair<double, double> > >
getAvgStretchVsTime(const double timeInterval, const double startAtTime,
                    const vector<shared_ptr<vector<vector<double> > > >& values)
{
    // "values" is a list of time2Stretch (as returned by the
    // "calculate..." functions) lists

    double curtime = startAtTime;

    // find the end time: the latest (largest) time among all data
    // points

    double endtime = -1;
    for (vector<shared_ptr<vector<vector<double> > > >::const_iterator it = values.begin();
         it != values.end(); ++it)
    {
        const vector<vector<double> >& time2stretch = *(*it);

        assert (time2stretch.back()[1] == 1);

        const double t = time2stretch.back()[0];
        if (t > endtime) {
            endtime = t;
        }
    }

    int count = values.size();
    assert (endtime > curtime);

    shared_ptr<vector<pair<double, double> > > time2AvgStretch =
        make_shared<vector<pair<double, double> > >();
                                             
    while (curtime <= endtime) {

        double sumOfStretches = 0;

        for (vector<shared_ptr<vector<vector<double> > > >::const_iterator it = values.begin();
             it != values.end(); ++it)
        {
            // this is a list like [(0.5, 1.66), (3.0, 1.33), (16.0, 1)]
            const vector<vector<double> >& time2Stretch = *(*it);

            // stretch at the "curtime". the goal is to figure out what
            // the stretch was at curtime.
            double curstretch = -1;

            // special optimization case
            if (curtime >= time2Stretch.back()[0]) {
                curstretch = time2Stretch.back()[1];
                sumOfStretches += curstretch;
                continue;
            }

            for (int i = 0; i < (time2Stretch.size() - 1); ++i) {
                const double leftTime = time2Stretch[i][0];
                assert (!(curtime < leftTime));
                if (time2Stretch[i].size() == 2) {
                    const double rightTime = time2Stretch[i+1][0];
                    if (leftTime <= curtime && curtime < rightTime) {
                        // then it's left stretch
                        curstretch = time2Stretch[i][1];
                        break;
                    }
                    else {
                        // check the next range
                        continue;
                    }
                }
                else {
                    const double rightTime = time2Stretch[i][2];
                    // for this one we use "<=" for both comparisons
                    // because this range is inclusive.
                    if (leftTime <= curtime && curtime <= rightTime) {
                        // then it's left stretch
                        const double left_stretch = time2Stretch[i][1];
                        const double right_stretch = time2Stretch[i][3];
                        const double slope = (right_stretch - left_stretch) /
                                             (rightTime - leftTime);
                        curstretch = slope*(curtime - leftTime) + left_stretch;
                        break;
                    }
                    else {
                        // check the next range
                        continue;
                    }
                }
            }
            if (curstretch == -1) {
                assert (curtime >= time2Stretch.back()[0]);
                curstretch = time2Stretch.back()[1];
            }
            sumOfStretches += curstretch;
        }

        double avgStretch = (sumOfStretches) / count;

        time2AvgStretch->push_back(make_pair(curtime, avgStretch));
        curtime += timeInterval;
    }

    return time2AvgStretch;
}

static shared_ptr<vector<pair<double, double> > >
getMaxStretchVsTime(const double timeInterval, const double startAtTime,
                    const vector<shared_ptr<vector<vector<double> > > >& values)
{
    // "values" is a list of time2Stretch (as returned by the
    // "calculate..." functions) lists

    double curtime = startAtTime;

    // find the end time: the latest (largest) time among all data
    // points

    double endtime = -1;
    for (vector<shared_ptr<vector<vector<double> > > >::const_iterator it = values.begin();
         it != values.end(); ++it)
    {
        const vector<vector<double> >& time2stretch = *(*it);

        assert (time2stretch.back()[1] == 1);

        const double t = time2stretch.back()[0];
        if (t > endtime) {
            endtime = t;
        }
    }

    assert (endtime > curtime);

    shared_ptr<vector<pair<double, double> > > time2MaxStretch =
        make_shared<vector<pair<double, double> > >();
                                             
    while (curtime <= endtime) {

        double maxstretch = -1;

        for (vector<shared_ptr<vector<vector<double> > > >::const_iterator it = values.begin();
             it != values.end(); ++it)
        {
            // this is a list like [(0.5, 1.66), (3.0, 1.33), (16.0, 1)]
            const vector<vector<double> >& time2Stretch = *(*it);

            // stretch at the "curtime". the goal is to figure out what
            // the stretch was at curtime.
            double curstretch = -1;

            // special optimization case
            if (curtime >= time2Stretch.back()[0]) {
                curstretch = time2Stretch.back()[1];
                if (curstretch > maxstretch) {
                    maxstretch = curstretch;
                }
                continue;
            }

            for (int i = 0; i < (time2Stretch.size() - 1); ++i) {
                const double leftTime = time2Stretch[i][0];
                assert (!(curtime < leftTime));
                if (time2Stretch[i].size() == 2) {
                    double rightTime = time2Stretch[i+1][0];
                    if (leftTime <= curtime && curtime < rightTime) {
                        // then it's left stretch
                        curstretch = time2Stretch[i][1];
                        break;
                    }
                    else {
                        // check the next range
                        continue;
                    }
                }
                else {
                    const double rightTime = time2Stretch[i][2];
                    // for this one we use "<=" for both comparisons
                    // because this range is inclusive.
                    if (leftTime <= curtime && curtime <= rightTime) {
                        // then it's left stretch
                        const double left_stretch = time2Stretch[i][1];
                        const double right_stretch = time2Stretch[i][3];
                        const double slope = (right_stretch - left_stretch) /
                                             (rightTime - leftTime);
                        curstretch = slope*(curtime - leftTime) + left_stretch;
                        break;
                    }
                    else {
                        // check the next range
                        continue;
                    }
                }
            }
            if (curstretch == -1) {
                assert (curtime >= time2Stretch.back()[0]);
                curstretch = time2Stretch.back()[1];
            }
            if (curstretch > maxstretch) {
                maxstretch = curstretch;
            }
        }

        time2MaxStretch->push_back(make_pair(curtime, maxstretch));
        curtime += timeInterval;
    }

    return time2MaxStretch;
}

static shared_ptr<vector<pair<double, double> > >
getFractionWithStretch1_VsTime(const double timeInterval, const double startAtTime,
                    const vector<shared_ptr<vector<vector<double> > > >& values)
{
    // "values" is a list of time2Stretch (as returned by the
    // "calculate..." functions) lists

    double curtime = startAtTime;

    // find the end time: the latest (largest) time among all data
    // points

    double endtime = -1;
    for (vector<shared_ptr<vector<vector<double> > > >::const_iterator it = values.begin();
         it != values.end(); ++it)
    {
        const vector<vector<double> >& time2stretch = *(*it);

        assert (time2stretch.back()[1] == 1);

        const double t = time2stretch.back()[0];
        if (t > endtime) {
            endtime = t;
        }
    }

    int count = values.size();
    assert (endtime > curtime);

    shared_ptr<vector<pair<double, double> > > time2FractionWithStretch1 =
        make_shared<vector<pair<double, double> > >();

    while (curtime <= endtime) {

        int countThatHaveConverged = 0;

        for (vector<shared_ptr<vector<vector<double> > > >::const_iterator it = values.begin();
             it != values.end(); ++it)
        {
            // this is a list like [(0.5, 1.66), (3.0, 1.33), (16.0, 1)]
            const vector<vector<double> >& time2Stretch = *(*it);

            // stretch at the "curtime". the goal is to figure out what
            // the stretch was at curtime.
            double curstretch = -1;

            // special optimization case
            if (curtime >= time2Stretch.back()[0]) {
                curstretch = time2Stretch.back()[1];
                assert (curstretch == 1);
                countThatHaveConverged++;
                continue;
            }

            for (int i = 0; i < (time2Stretch.size() - 1); ++i) {
                const double leftTime = time2Stretch[i][0];
                assert (!(curtime < leftTime));
                if (time2Stretch[i].size() == 2) {
                    double rightTime = time2Stretch[i+1][0];
                    if (leftTime <= curtime && curtime < rightTime) {
                        // then it's left stretch
                        curstretch = time2Stretch[i][1];
                        break;
                    }
                    else {
                        // check the next range
                        continue;
                    }
                }
                else {
                    const double rightTime = time2Stretch[i][2];
                    // for this one we use "<=" for both comparisons
                    // because this range is inclusive.
                    if (leftTime <= curtime && curtime <= rightTime) {
                        // then it's left stretch
                        const double left_stretch = time2Stretch[i][1];
                        const double right_stretch = time2Stretch[i][3];
                        const double slope = (right_stretch - left_stretch) /
                                             (rightTime - leftTime);
                        curstretch = slope*(curtime - leftTime) + left_stretch;
                        break;
                    }
                    else {
                        // check the next range
                        continue;
                    }
                }
            }
            if (curstretch == -1) {
                assert (curtime >= time2Stretch.back()[0]);
                curstretch = time2Stretch.back()[1];
            }
            if (curstretch == 1) {
                countThatHaveConverged++;
            }
        }

        time2FractionWithStretch1->push_back(
            make_pair(curtime, ((double)countThatHaveConverged) / count));
        curtime += timeInterval;
    }

    return time2FractionWithStretch1;
}

/* -------------------------------------------------------- */

static bool
sanityCheckValues(const double timeInterval, const double startAtTime,
                  const vector<shared_ptr<vector<vector<double> > > >& values)
{
//    double curtime = startAtTime;

    for (vector<shared_ptr<vector<vector<double> > > >::const_iterator it = values.begin();
         it != values.end(); ++it)
    {
        const vector<vector<double> >& lst = *(*it);
        assert (lst.back()[1] == 1);
        for (int i = 0; i < (lst.size() - 1); ++i) {
            if (lst[i].size() == 2) {
                // the time must be non-negative and increasing
                assert (lst[i][0] >= 0 && lst[i][0] < lst[i+1][0]);
            }
            else {
                assert (0 <= lst[i][0] && lst[i][0] < lst[i][2] && lst[i][2] < lst[i+1][0]);
            }
            if (i > 0) {
                if (lst[i].size() == 2) {
                    assert (lst[i][1] >= lst[i+1][1]);
                }
                else {
                    assert (lst[i][1] > lst[i][3] && lst[i][3] > lst[i+1][1]);
                }
            }
        }
    }
    return true;
}

/* -------------------------------------------------------- */

/* we have observed this behavior: when we remove two arcs, all other
 * arc ids are not affected, as expected. when we immediately add the two arcs
 * back, they will reuse their two old arc ids, though might be in
 * different order; thus all other arc ids are also not affected, as
 * expected.
 */
static bool
testEdgeRemoval(const char* graphFilePath, const bool weighted)
{
    bool ok = false;
    Graph_t g;
    WeightMap_t weights(g, 1);
    Random linkrandom(time(NULL));

    cout << "begin " << __func__ << endl;

    load_graph(
        graphFilePath,
        g,
        weighted,
        weights,
	NULL,
	NULL);

    cout << "graphFilePath: " << graphFilePath << endl;
    cout << "num nodes: " << countNodes(g) << endl;
    cout << "num arcs: " << countArcs(g) << endl;

    for (int i = 0; i < 4; ++i) {
        // all arcs, all directions.
        vector<Arc_t> arcsVec;
        map<int, tuple<Node_t, Node_t, double> > arc2AttrsMap;
        for (Graph_t::ArcIt ait(g); ait != INVALID; ++ait) {
            arcsVec.push_back(ait);
            arc2AttrsMap[g.id(ait)] = make_tuple(
                g.source(ait), g.target(ait), weights[ait]);
        }
        assert ((arcsVec.size()) == countArcs(g));

        // pick a random edge, i.e., pair of arcs and remember the two arc
        // ids.
        Arc_t arc_uv = arcsVec[linkrandom.integer(arcsVec.size())];
        int arc_uv_id = g.id(arc_uv);
        Node_t u = g.source(arc_uv);
        Node_t v = g.target(arc_uv);
        Arc_t reverse_arc = findArc(g, v, u);
        int reverse_arc_id = g.id(reverse_arc);

        cout << "test removing edge ("
             << g.id(u) << ", " << g.id(v) << ")" << endl;

        // get the shortest paths between u and v, which must have
        // same lengths, but can be > 1.
        Path_t p_uv_b4;
        Path_t p_vu_b4;
        assert (dijkstra(g, weights).path(p_uv_b4).run(u, v));
        assert (dijkstra(g, weights).path(p_vu_b4).run(v, u));
        assert (p_uv_b4.length() == p_vu_b4.length());
        // get the path of nodes so we can compare before removal and
        // after adding back. because adding back might swap the arc
        // ids, and the Path_t contains path ids, the comparison of
        // Path_t might fail. but the all node ids are the same since
        // we dont remove nodes.
        PathOfNodes_t pon_uv_b4 = *getPrefixNodes(g, p_uv_b4);
        PathOfNodes_t pon_vu_b4 = *getPrefixNodes(g, p_vu_b4);

        /////////////// remove the edge
        double savedEdgeAttr = removeEdge(g, u, v, weights);

        /////////////// make sure it removes only those two arcs
        assert ((arcsVec.size() - 2) == countArcs(g));
        for (vector<Arc_t>::const_iterator ait = arcsVec.begin();
             ait != arcsVec.end(); ++ait)
        {
            const Arc_t& a = *ait;
            const int aid = g.id(a);
            if (aid == arc_uv_id || aid == reverse_arc_id) {
                // skip
                continue;
            }
            // make sure it has the same end points as before removal
            const tuple<Node_t, Node_t, double>& attrs = arc2AttrsMap[aid];
            assert (g.source(a) == attrs.get<0>());
            assert (g.target(a) == attrs.get<1>());
            assert (weights[a] == attrs.get<2>());
        }

        Path_t p_uv_2;
        Path_t p_vu_2;
        // the 2 nodes might become disconnected
        if (dijkstra(g, weights).path(p_uv_2).run(u, v)) {
            assert (dijkstra(g, weights).path(p_vu_2).run(v, u));
            assert (p_uv_2.length() == p_vu_2.length());
        }

        //////////////// now, add them back
        addEdge(g, u, v, weights, savedEdgeAttr);

        // make sure the two added arcs used the same ids and have save
        // weights as before. its ok for their ids to be swapped.
        Arc_t new_arc_uv = findArc(g, u, v);
        Arc_t new_reverse_arc = findArc(g, v, u);

        assert (g.id(new_arc_uv) == arc_uv_id ||
                g.id(new_arc_uv) == reverse_arc_id);
        assert (g.id(new_reverse_arc) == arc_uv_id ||
                g.id(new_reverse_arc) == reverse_arc_id);
        assert (g.id(new_arc_uv) != g.id(new_reverse_arc));
        assert (weights[new_arc_uv] == arc2AttrsMap[arc_uv_id].get<2>());
        assert (weights[new_reverse_arc] ==
                arc2AttrsMap[reverse_arc_id].get<2>());

        // get the shortest paths between u and v, which be exactly
        // like the original paths before removal
        Path_t p_uv_after;
        Path_t p_vu_after;
        assert (dijkstra(g, weights).path(p_uv_after).run(u, v));
        assert (dijkstra(g, weights).path(p_vu_after).run(v, u));
        PathOfNodes_t pon_uv_after = *getPrefixNodes(g, p_uv_after);
        PathOfNodes_t pon_vu_after = *getPrefixNodes(g, p_vu_after);
        assert (pon_uv_b4 == pon_uv_after);
        assert (pon_vu_b4 == pon_vu_after);
    }

    cout << __func__ << "() passed.\n" << endl;
    
    ok = true;
    return ok;
}

/* -------------------------------------------------------- */
#include <getopt.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{

    Graph_t g;
    WeightMap_t weights(g, 1);
    int linkStartIdx = -1, linkEndIdx = -1;
    double timeOfFailure = -1, passThruDelay = -1;
    double spfDelay = -1, spfComputeTime = -1, fibUpdateTime = -1;
    int linkSampleSize = -1;
    int linkSeed = -1;
    int srcSampleSize = -1, srcSeed = -1;
    int maxSrcsToTryPerLink = -1;
    int dstSampleSize = -1, dstSeed = -1;
    const char* graphFilePath = NULL;
    const char* outputDir = NULL;
    double min_edge_weight = 9999999;
    double max_edge_weight = -9999999;
    Random linkrandom, srcrandom, dstrandom;
    int weighted = 1;
    int opt;
    int long_index;
    string scheme;
    set<string> schemesToEval;

    struct option long_options[] = {
        {"weighted", no_argument, &weighted, 1},
        {"timeOfFailure", required_argument, 0, 1000},
        {"passThruDelay", required_argument, 0, 1002},
        {"linkStartIdx", required_argument, 0, 1003},
        {"linkEndIdx", required_argument, 0, 1004},
        {"linkSampleSize", required_argument, 0, 1005},
        {"linkSeed", required_argument, 0, 1006},
        {"srcSampleSize", required_argument, 0, 1007},
        {"srcSeed", required_argument, 0, 1008},
        {"dstSampleSize", required_argument, 0, 1009},
        {"dstSeed", required_argument, 0, 1010},
        {"outputDir", required_argument, 0, 1011},
        {"maxSrcsToTryPerLink", required_argument, 0, 1012},
        {"spfDelay", required_argument, 0, 1013},
        {"spfComputeTime", required_argument, 0, 1014},
        {"fibUpdateTime", required_argument, 0, 1015},
        {"scheme", required_argument, 0, 1016},
        {0, 0, 0, 0},
    };
    while ((opt = getopt_long(argc, argv, "", long_options, &long_index)) != -1)
    {
        switch (opt) {
        case 0:
            if (long_options[long_index].flag != 0) {
                break;
            }
            cout << "option " << long_options[long_index].name;
            if (optarg) {
                cout << " with arg " << optarg;
            }
            cout << endl;
            break;

        case 1000:
            timeOfFailure = strtod(optarg, NULL);
            break;

        case 1002:
            passThruDelay = strtod(optarg, NULL);
            break;

        case 1003:
            linkStartIdx = strtol(optarg, NULL, 10);
            break;

        case 1004:
            linkEndIdx = strtol(optarg, NULL, 10);
            break;

        case 1005:
            linkSampleSize = strtol(optarg, NULL, 10);
            break;

        case 1006:
            linkSeed = strtol(optarg, NULL, 10);
            break;

        case 1007:
            srcSampleSize = strtol(optarg, NULL, 10);
            break;

        case 1008:
            srcSeed = strtol(optarg, NULL, 10);
            break;

        case 1009:
            dstSampleSize = strtol(optarg, NULL, 10);
            break;

        case 1010:
            dstSeed = strtol(optarg, NULL, 10);
            break;

        case 1011:
            outputDir = optarg;
            break;

        case 1012:
            maxSrcsToTryPerLink = strtol(optarg, NULL, 10);
            break;

        case 1013:
            spfDelay = strtod(optarg, NULL);
            break;

        case 1014:
            spfComputeTime = strtod(optarg, NULL);
            break;

        case 1015:
            fibUpdateTime = strtod(optarg, NULL);
            break;

        case 1016:
            scheme = optarg;
	    if (scheme == "all") {
	      schemesToEval = known_schemes;
	    }
	    else {
	      assert (inSet(known_schemes, scheme));
	      schemesToEval.insert(scheme);
	    }
            break;

        default:
            exit(-1);
            break;
        }
    }

    graphFilePath = argv[optind];
    assert (graphFilePath != NULL);
    assert (outputDir != NULL);

    if (schemesToEval.size() == 0) {
      cout << "!! must specify at least one scheme to evaluate (--scheme option).\n";
      cout << "supported schemes are:\n";
      std::copy(known_schemes.begin(),
		known_schemes.end(),
		std::ostream_iterator<string>(std::cout, ", "));
      cout << "\nor use \"all\" to evaluate all known schemes.\n";
      exit(-1);
    }

    assert (timeOfFailure >= 0 && spfDelay >= 0 && spfComputeTime >= 0 && fibUpdateTime >= 0 && passThruDelay >= 0);

    assert (testEdgeRemoval(graphFilePath, weighted == 1));

    load_graph(
        graphFilePath,
        g,
        weighted == 1,
        weights,
	&min_edge_weight,
	&max_edge_weight
	       );

    ////// get all the unique "u->v" edges. i.e., we only want one or the other
    ////// of (u->v) and (v->u), not both.
    set<Arc_t> edgesSet;
    for (Graph_t::ArcIt ait(g); ait != INVALID; ++ait) {
        const Node_t& u = g.source(ait);
        const Node_t& v = g.target(ait);
        const Arc_t& reverse_a = findArc(g, v, u);
        if (edgesSet.end() == edgesSet.find(reverse_a)) {
            // if reverse arc is not there, then insert this arc
            edgesSet.insert(ait);
        }
    }
    assert ((edgesSet.size() * 2) == countArcs(g));

    if (linkStartIdx == -1) {
        linkStartIdx = 0;
    }
    if (linkEndIdx == -1) {
        linkEndIdx = edgesSet.size() - 1;
    }
    assert ((0 <= linkStartIdx) && (linkStartIdx <= linkEndIdx) &&
            (linkEndIdx <= (edgesSet.size() - 1)));

    if (linkSampleSize == -1) {
        linkSampleSize = linkEndIdx - linkStartIdx + 1;
    }
    assert (1 <= linkSampleSize);
    assert (linkSampleSize <= (linkEndIdx - linkStartIdx + 1));

    if (srcSampleSize != -1) {
        assert (0 < srcSampleSize && srcSampleSize <= countNodes(g));
        assert (srcSampleSize <= maxSrcsToTryPerLink);
    }

    if (dstSampleSize != -1) {
        assert (0 < dstSampleSize && dstSampleSize <= countNodes(g));
    }

    if (linkSeed == -1) {
        linkSeed = time(NULL);
    }
    linkrandom.seed(linkSeed);

    if (srcSeed == -1) {
        srcSeed = time(NULL);
    }
    srcrandom.seed(srcSeed);

    if (dstSeed == -1) {
        dstSeed = time(NULL);
    }
    dstrandom.seed(dstSeed);

    assert (0 == mkdir(outputDir, 0777));

    ofstream paramsfile ((string() + outputDir + "/params.txt").c_str());
    ostream* outputstreams[] = {&cout, &paramsfile};
    for (int i = 0; i < ARRAY_LENGTH(outputstreams); ++i) {
        ostream& os = *outputstreams[i];
        os << "code version: " << Id << endl;
        os << "boost version: " << EXPAND_AND_QUOTE(BOOST_VERSION) << endl;
        os << "lemon version: " << EXPAND_AND_QUOTE(LEMON_VERSION) "" << endl;
        os << endl;
        for (int j = 0; j < argc; ++j) {
            os << argv[j] << " ";
        }
        os << endl << endl;
        os << "graphFilePath: " << graphFilePath << endl;
        os << "weighted: " << (weighted == 1 ? "true" : "false") << endl;
        os << "node count: " << (countNodes(g)) << endl;
        os << "arc count: " << countArcs(g) << endl;
        os << "min_edge_weight: " << min_edge_weight << endl;
        os << "max_edge_weight: " << max_edge_weight << endl;
        os << "outputDir: " << outputDir << endl;
        os << endl;
        os << "linkStartIdx: " << linkStartIdx << endl;
        os << "linkEndIdx: " << linkEndIdx << endl;
        os << "linkSampleSize: " << linkSampleSize << endl;
        os << "linkSeed: " << linkSeed << endl;
        os << endl;
        os << "srcSampleSize: " << srcSampleSize << " => " << (srcSampleSize == -1 ? "ALL" : "sampling") << " sources" << endl;
        os << "maxSrcsToTryPerLink: " << maxSrcsToTryPerLink << endl;
        os << "srcSeed: " << srcSeed << endl;
        os << endl;
        os << "dstSampleSize: " << dstSampleSize << endl;
        os << "dstSeed: " << dstSeed << endl;
        os << endl;
        os << "timeOfFailure: " << timeOfFailure << endl;
        os << "spfDelay: " << spfDelay << endl;
        os << "spfComputeTime: " << spfComputeTime << endl;
        os << "fibUpdateTime: " << fibUpdateTime << endl;
        os << "passThruDelay: " << passThruDelay << endl;
        os << endl;
	os << "schemesToEval: ";
	std::copy(schemesToEval.begin(),
		  schemesToEval.end(),
		  std::ostream_iterator<string>(os, " "));
	os << endl;
    }

    paramsfile.close();

    // need the edges in vector so we can get (random) index
    vector<Arc_t> edgesVec(edgesSet.size());
    copy(edgesSet.begin(), edgesSet.end(), edgesVec.begin());
    edgesSet.clear();
    // sort
    sort(edgesVec.begin(), edgesVec.end());
    // keep only the arcs in the specified range:
    // first, erase from the end
    edgesVec.erase(edgesVec.begin()+linkEndIdx+1, edgesVec.end());
    // now erase from the front
    edgesVec.erase(edgesVec.begin(), edgesVec.begin()+linkStartIdx);

    vector<shared_ptr<vector<vector<double> > > > safeguard_results;
    vector<shared_ptr<vector<vector<double> > > > fastdag_results;
    vector<shared_ptr<vector<vector<double> > > > slowdag_results;
    vector<shared_ptr<vector<vector<double> > > > floodeddag_results;
    vector<shared_ptr<vector<vector<double> > > > fastvsr_results;

    map<string, vector<shared_ptr<vector<vector<double> > > >* > schemeToResult = map_list_of
            ("SafeGuard", &safeguard_results)
            ("Fast-DAG", &fastdag_results)
            ("Slow-DAG", &slowdag_results)
            ("Flooded-DAG", &floodeddag_results)
            ("Fast-VSR", &fastvsr_results);
            
    map<string, calculatorFunc_t> schemeToCalcFunc = map_list_of
            ("SafeGuard", calculateForSafeGuard)
            ("Fast-DAG", calculateForFastDAG_wrapper)
            ("Slow-DAG", calculateForSlowDAG_wrapper)
            ("Flooded-DAG", calculateForFloodedDAG_wrapper)
            ("Fast-VSR", calculateForFastVSR);

    map<string, shared_ptr<ofstream> > schemeToRawOutFile;

    // open the raw data files for output
    for (set<string>::iterator iter = schemesToEval.begin();
	 iter != schemesToEval.end(); ++iter)
    {
        const string& schemename = *iter;
        string filepath = string() + outputDir + "/raw_" + schemename + ".txt";
        schemeToRawOutFile[schemename] = make_shared<ofstream>(filepath.c_str());
        (*schemeToRawOutFile[schemename])
            << "# comment lines start with a #" << endl
            << "# code rev: " << Id << endl
            << "# boost version: " << EXPAND_AND_QUOTE(BOOST_VERSION) << endl
            << "# lemon version: " << EXPAND_AND_QUOTE(LEMON_VERSION) << endl
            << "# graph file: " << graphFilePath << endl
            << "# link range: " << linkStartIdx << ", " << linkEndIdx << endl
            << "# timeOfFailure: " << timeOfFailure << endl
            << "# spfDelay: " << spfDelay << endl
            << "# spfComputeTime: " << spfComputeTime << endl
            << "# fibUpdateTime: " << fibUpdateTime << endl
            << "# passThruDelay: " << passThruDelay << endl
            << "# scheme: " << schemename << endl
            << "#" << endl;
    }

    assert (linkSampleSize <= edgesVec.size());
    for (int i = 0; i < linkSampleSize; ++i) {
        const uint32_t idx = linkrandom.integer(edgesVec.size());
        const Arc_t& arc = edgesVec[idx];
        // remove so we don't sample it again
        edgesVec.erase(edgesVec.begin() + idx);
        const Node_t& u = g.source(arc);
        const Node_t& v = g.target(arc);
        for (map<string, shared_ptr<ofstream> >::iterator sit = schemeToRawOutFile.begin();
             sit != schemeToRawOutFile.end(); ++sit)
        {
            *(sit->second) << "# " << i << "th edge, " << g.id(u) << ", "
                           << g.id(v) << endl;
        }

        // do all sources or do sampling
        Graph_t::NodeIt sit(g);
        Node_t s;
        int numTriedSrcs = 0;
        int numGoodSrcs = 0;
        shared_ptr<vector<shared_ptr<PathOfNodes_t> > > pathsThatUseEdge;

        // gather all nodes into vector, sorted.

        // haven't profiled performance of this loop yet, but assuming
        // that the link sample is small (no more than a few 100's),
        // so that this reinitialization of allNodeIdsVec is
        // insignificant compared to total running time.
        vector<int> allNodeIdsVec;
        if (srcSampleSize > 0) {
            allNodeIdsVec.reserve(countNodes(g));
            for (Graph_t::NodeIt nit(g); nit != INVALID; ++nit) {
                // yes, need to use push_back here because "reserve"
                // only changes the capacity, not actual size of vec.
                allNodeIdsVec.push_back(g.id(nit));
            }
            sort(allNodeIdsVec.begin(), allNodeIdsVec.end());
        }

get_one_src:
        if (srcSampleSize <= 0) {
            // do all sources, so just get the next one in sequence
            if (sit == INVALID) {
                // to next edge
                continue;
            }
            else {
                s = sit;
                ++sit;
                pathsThatUseEdge = getPathsThatUseEdge(
                    g, weights, s, arc, dstSampleSize, &dstrandom);
            }
        }
        else {
            if (numTriedSrcs >= maxSrcsToTryPerLink) {
                // do not want to try anymore, give up.
                continue;
                // to next edge
            }
            if (numGoodSrcs >= srcSampleSize) {
                // we've got enough srcs as requested, done as well.
                continue;
                // to next edge
            }
            // now, find a random source that has at least ONE path
            // that uses the link
            do {
                uint32_t s_idx = srcrandom.integer(allNodeIdsVec.size());
                // remove so we don't sample it again
                allNodeIdsVec.erase(allNodeIdsVec.begin() + s_idx);
                s = g.nodeFromId(s_idx);
                numTriedSrcs++;
                pathsThatUseEdge = getPathsThatUseEdge(
                    g, weights, s, arc, dstSampleSize, &dstrandom);
            }
            while ((numTriedSrcs < maxSrcsToTryPerLink) && (pathsThatUseEdge->size() == 0));

            if (pathsThatUseEdge->size() > 0) {
                numGoodSrcs++;
            }
            else if (numTriedSrcs >= maxSrcsToTryPerLink) {
                // do not want to try anymore, give up
                continue;
                // to next edge
            }
        }

        {
            // do all paths that use the edge in either direction
            for (vector<shared_ptr<PathOfNodes_t> >::const_iterator pit = pathsThatUseEdge->begin();
                 pit != pathsThatUseEdge->end(); ++pit)
            {
                const shared_ptr<PathOfNodes_t>& p = *pit;
                const Node_t& d = p->back();
                // fn1 is same as r0 in the paper, i.e., the router at
                // the failed link and is closer to the source than
                // fn2 is.
                Node_t fn1, fn2;
                int fn1Idx = -1;
                const int uIdx = find(p->begin(), p->end(), u) - p->begin();
                const int vIdx = find(p->begin(), p->end(), v) - p->begin();
                if (uIdx < vIdx) {
                    fn1 = u;
                    fn2 = v;
                    fn1Idx = uIdx;
                }
                else {
                    fn1 = v;
                    fn2 = u;
                    fn1Idx = vIdx;
                }
                const double savedEdgeAttr = removeEdge(g, fn1, fn2, weights);
                double shortestLengthWithFailure = -1;
                const bool reached = dijkstra(
                    g, weights).dist(shortestLengthWithFailure).run(s, d);
                if (!reached) {
                    addEdge(g, fn1, fn2, weights, savedEdgeAttr);
                    continue;
                }

                // prepare the preCalculatedPathLengthsDict
                map<Node_t, map<Node_t, double> > preCalculatedPathLengthsDict;
                for (int j = fn1Idx; j > -1; --j) {
                    const Node_t& r = (*p)[j];
                    const Node_t targets[] = {s, d, fn1};
                    for (int k = 0; k < ARRAY_LENGTH(targets); ++k) {
                        const Node_t& target = targets[k];
                        double distance = -1;
                        dijkstra(g, weights).dist(distance).run(r, target);
                        preCalculatedPathLengthsDict[r][target] = distance;
                    }
                }
                // run the calculators
                for (set<string>::iterator cfit = schemesToEval.begin();
                     cfit != schemesToEval.end(); ++cfit)
                {
                    const string& schemename = *cfit;
                    calculatorFunc_t calcfunc = schemeToCalcFunc[schemename];
                    shared_ptr<vector<vector<double> > > result = (*calcfunc)(
                        *p, fn1,
                        shortestLengthWithFailure,
                        preCalculatedPathLengthsDict,
                        spfDelay,
                        spfComputeTime,
                        fibUpdateTime,
                        passThruDelay,
                        timeOfFailure);
                    schemeToResult[schemename]->push_back(result);
                    // output the result as well as commented line on
                    // the (link, s, d) triple
                    ofstream& rawoutfile = *(schemeToRawOutFile[schemename]);
                    outputTime2Stretch(rawoutfile, *result);
                }
                // restore edge
                addEdge(g, fn1, fn2, weights, savedEdgeAttr);
            }
        }

        goto get_one_src;
    }
    // output the max, avg, etc to files
    for (set<string>::iterator sit = schemesToEval.begin();
         sit != schemesToEval.end(); ++sit)
    {
        const string& schemename = *sit;
        string filepath;
        ofstream myfile;

        double timeInterval = 1.0;
        double startAtTime = 0.0;
        sanityCheckValues(timeInterval, startAtTime, *(schemeToResult[schemename]));

        /* //we already output the raw result as we go

        for (vector<shared_ptr<vector<vector<double> > > >::iterator rit = schemeToResult[schemename]->begin();
             rit != schemeToResult[schemename]->end(); ++rit)
        {
            outputTime2Stretch(myfile, *(*rit));
        }
        */

        filepath = string() + outputDir + "/avgStretch_" + schemename + ".txt";
        myfile.open(filepath.c_str());
        shared_ptr<vector<pair<double, double> > > datapoints =
            getAvgStretchVsTime(1, 0, *(schemeToResult[schemename]));
        for (vector<pair<double, double> >::const_iterator it = datapoints->begin();
             it != datapoints->end(); ++it)
        {
            myfile << (*it).first << "," << (*it).second << "\n";
        }

        // maxstretch
        myfile.close();
        filepath = string() + outputDir + "/maxStretch_" + schemename + ".txt";
        myfile.open(filepath.c_str());
        datapoints = getMaxStretchVsTime(1, 0, *(schemeToResult[schemename]));
        for (vector<pair<double, double> >::const_iterator it = datapoints->begin();
             it != datapoints->end(); ++it)
        {
            myfile << (*it).first << "," << (*it).second << "\n";
        }

        // fractionConverged
        myfile.close();
        filepath = string() + outputDir + "/fractionWithStretch1_" + schemename + ".txt";
        myfile.open(filepath.c_str());
        datapoints = getFractionWithStretch1_VsTime(1, 0, *(schemeToResult[schemename]));
        for (vector<pair<double, double> >::const_iterator it = datapoints->begin();
             it != datapoints->end(); ++it)
        {
            myfile << (*it).first << "," << (*it).second << "\n";
        }
    }
    return 0;
}
