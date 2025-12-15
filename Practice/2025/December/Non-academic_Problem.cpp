#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const long long inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
const int N = 1e5 + 2;
vector<vector<int>> g(N);
vector<set<int>> t;
vector<pair<int,int>> edges(N);
set<pair<int,int>> bridges;
int dfs_num[N], color[N], dfs_low[N], dfs_cnt = 0, parent[N], value[N], subtree_size[N], len;
vector<bool> visited(N);
long long ans;

void assign(int n){
	ans = inf;
	for(int i = 0; i < n; i++){
		visited[i] = false;
		g[i].clear();
		dfs_num[i] = -1;
		color[i] = 0;
	}
	dfs_cnt = 0;
	bridges.clear();
	t.clear();
}

void find_bridges(int node, int par){
	dfs_num[node] = dfs_cnt++;
	dfs_low[node] = dfs_num[node];
	for(auto &adj: g[node]){
		if(dfs_num[adj] == -1){
			find_bridges(adj, node);
			if(dfs_low[adj] > dfs_num[node]){
				bridges.insert({adj, node});
				bridges.insert({node, adj});
				color[adj] = color[node] = 1;
			}
			dfs_low[node] = min(dfs_low[node],dfs_low[adj]);
		}else if(adj != par){
			dfs_low[node] = min(dfs_low[node], dfs_num[adj]);
		}
	}
}

void dfs(int node, int par){
	visited[node] = true;
	parent[node] = par;
	for(auto &adj: g[node]){
		if(!visited[adj]){
			if(bridges.count(make_pair(adj, node)))
				dfs(adj, adj);
			else
				dfs(adj, par);
		}
	} 
}

long long count_pair(long long x){
	return (x * (x - 1)) / 2;
}

void dfs_subtree_size(int node, int par){
	subtree_size[node] = value[node];
	for(auto &child: t[node]){
		if(child != par){
			dfs_subtree_size(child, node);
			subtree_size[node] += subtree_size[child];
		}
	}
	ans = min(ans, count_pair(subtree_size[node]) + count_pair(len - subtree_size[node]));
}

void solve()
{
	int n,m;
	cin >> n >> m;
	len = n;
	assign(n);
	for(int i = 0; i < m; i++){
		auto &[u,v] = edges[i];
		cin >> u >> v;
		u--, v--;
		g[u].push_back(v);
		g[v].push_back(u);
	}
	find_bridges(0, -1);
	if(bridges.empty()){
		cout << (n * (n - 1)) / 2 << endl;
		return;
	}
	int tree_size = 0;
	map<int,int> id;
	for(int i = 0; i < n; i++){
		if(color[i]){
			value[tree_size] = 0;
			id[i] = tree_size;
			tree_size++;
		}
	}
	t.resize(tree_size);
	dfs((*bridges.begin()).first, (*bridges.begin()).first);
	for(int i = 0; i < n; i++){
		value[id[parent[i]]]++;
	}
	for(int i = 0; i < m; i++){
		auto &[u,v] = edges[i];
		if(parent[u] != parent[v]){
			t[id[parent[u]]].insert(id[parent[v]]);
			t[id[parent[v]]].insert(id[parent[u]]);
		}
	}
	dfs_subtree_size(0, -1);
	cout << ans << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}