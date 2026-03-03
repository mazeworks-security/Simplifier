using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace Mba.Simplifier.Verification
{
    public enum XmgNodeType { PI, MAJ, XOR3 }

    public struct XmgSignal
    {
        public int NodeIndex;
        public bool IsComplemented;

        public override string ToString() => (IsComplemented ? "-" : "") + NodeIndex;
    }

    public class XmgNode
    {
        public int Id;
        public XmgNodeType Type;
        public XmgSignal[] Children;

        public XmgNode(int id, XmgNodeType type, XmgSignal[] children = null)
        {
            Id = id;
            Type = type;
            Children = children ?? Array.Empty<XmgSignal>();
        }
    }

    public class XmgNetwork
    {
        public Dictionary<int, XmgNode> Nodes = new Dictionary<int, XmgNode>();
        public List<int> PIs = new List<int>();
        public List<XmgSignal> POs = new List<XmgSignal>();

        public void AddPI(int id)
        {
            Nodes[id] = new XmgNode(id, XmgNodeType.PI);
            PIs.Add(id);
        }

        public void AddGate(int id, string typeStr, XmgSignal[] children)
        {
            var type = typeStr == "MAJ" ? XmgNodeType.MAJ : XmgNodeType.XOR3;
            Nodes[id] = new XmgNode(id, type, children);
        }

        public void AddPO(XmgSignal signal)
        {
            POs.Add(signal);
        }
    }

    public class XmgParser
    {
        private static readonly Regex PiRegex = new Regex(@"INPUT\((\d+)\)");
        private static readonly Regex PoRegex = new Regex(@"OUTPUT\(\d+\) = (-?\d+)");
        private static readonly Regex GateRegex = new Regex(@"(\d+) = (MAJ|XOR3)\((.+)\)");

        public static XmgNetwork Parse(string filePath)
        {
            var network = new XmgNetwork();
            foreach (var line in File.ReadLines(filePath))
            {
                if (string.IsNullOrWhiteSpace(line)) continue;

                var piMatch = PiRegex.Match(line);
                if (piMatch.Success)
                {
                    network.AddPI(int.Parse(piMatch.Groups[1].Value));
                    continue;
                }

                var poMatch = PoRegex.Match(line);
                if (poMatch.Success)
                {
                    network.AddPO(ParseSignal(poMatch.Groups[1].Value));
                    continue;
                }

                var gateMatch = GateRegex.Match(line);
                if (gateMatch.Success)
                {
                    int id = int.Parse(gateMatch.Groups[1].Value);
                    string type = gateMatch.Groups[2].Value;
                    var kids = gateMatch.Groups[3].Value
                        .Split(',')
                        .Select(s => ParseSignal(s.Trim()))
                        .ToArray();
                    network.AddGate(id, type, kids);
                }
            }
            return network;
        }

        private static XmgSignal ParseSignal(string s)
        {
            bool combined = s.StartsWith("-");
            int id = int.Parse(combined ? s.Substring(1) : s);
            return new XmgSignal { NodeIndex = id, IsComplemented = combined };
        }
    }
}
