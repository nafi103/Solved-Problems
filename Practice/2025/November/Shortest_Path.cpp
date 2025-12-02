#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
	int n, m, k;
	cin >> n >> m >> k;
    map<pair<int,int> , set<int>> forbidden;
    vector<vector<int>> g(n+1);
    while(m--){
    	int u,v;
    	cin >> u >> v;
    	g[u].push_back(v);
    	g[v].push_back(u);
    }
    vector<vector<bool>> visited(n+1, vector<bool> (n+1, false));
    map<pair<int,int>, pair<int,int>> parent;
    while(k--){
    	int a, b, c;
    	cin >> a >> b >> c;
    	forbidden[{a,b}].insert(c);
    }
    queue<array<int, 3>> q;
    q.push({0, 1, 0});
    int dist = inf;
    while(!q.empty()){
    	auto [par, node, d] = q.front();
    	q.pop();
    	if(node == n){
    		dist = d;
    		break;
    	}
    	set<int> &ref = forbidden[{par,node}];
    	for(auto &adj: g[node]){
    		if(ref.count(adj) or visited[node][adj])
    			continue;
    		visited[node][adj] = true;
    		parent[{adj, d+1}] = {node, d};
    		q.push({node, adj, d+1});
    	}
    }
    if(dist == inf){
    	cout << -1 << endl;
    	return;
    }
    vector<int> path;
    pair<int,int> curr = {n, dist};
    while(curr.first != 0){
    	path.push_back(curr.first);
    	curr = parent[curr];
    }
    reverse(all(path));
    cout<< sz(path) - 1 <<endl;
    for(auto &node: path)
    	cout << node << " ";
    cout << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}