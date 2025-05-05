#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
const int N = 2e5 + 5;
const int D = 19;
const int S = (1 << D);

int n, q;
vector<int>value;
vector<vector<int>> t;

int subtree_size[N], parent[N], level[N];
int st[S], id[N], tp[N];

void update(int idx, int val) {
	st[idx += n] = val;
	for (idx /= 2; idx; idx /= 2) st[idx] = max(st[2 * idx], st[2 * idx + 1]);
}

int query(int lo, int hi) {
	int ra = 0, rb = 0;
	for (lo += n, hi += n + 1; lo < hi; lo /= 2, hi /= 2) {
		if (lo & 1) ra = max(ra, st[lo++]);
		if (hi & 1) rb = max(rb, st[--hi]);
	}
	return max(ra, rb);
}

int dfs_subtree_size(int node, int par) {
	subtree_size[node] = 1;
	parent[node] = par;
	for (int chi : t[node]) {
		if (chi == par) continue;
		level[chi] = level[node] + 1;
		parent[chi] = node;
		subtree_size[node] += dfs_subtree_size(chi, node);
	}
	return subtree_size[node];
}

int ct = 1;

void dfs_hld(int node, int par, int top) {
	id[node] = ct++;
	tp[node] = top;
	update(id[node], value[node]);
	int h_chi = -1, h_subtree_size = -1;
	for (int chi : t[node]) {
		if (chi == par) continue;
		if (subtree_size[chi] > h_subtree_size) {
			h_subtree_size = subtree_size[chi];
			h_chi = chi;
		}
	}
	if (h_chi == -1) return;
	dfs_hld(h_chi, node, top);
	for (int chi : t[node]) {
		if (chi == par || chi == h_chi) continue;
		dfs_hld(chi, node, chi);
	}
}

int path(int x, int y) {
	int ret = 0;
	while (tp[x] != tp[y]) {
		if (level[tp[x]] < level[tp[y]]) swap(x, y);
		ret = max(ret, query(id[tp[x]], id[x]));
		x = parent[tp[x]];
	}
	if (level[x] > level[y]) swap(x, y);
	ret = max(ret, query(id[x], id[y]));
	return ret;
}


void solve()
{
    cin>>n>>q;
    t.resize(n+1);
    value.resize(n+1);
	for (int i = 1; i <= n; i++) cin>>value[i];
	for (int i = 1; i < n; i++) {
		int a, b;
        cin>>a>>b;
		t[a].push_back(b);
		t[b].push_back(a);
	}
    debug(t)
	dfs_subtree_size(1, 1);
	dfs_hld(1, 1, 1);
	while (q--) {
		int t;
        cin>>t;
		if (t == 1) {
			int s, x;
            cin>>s>>x;
			value[s] = x;
			update(id[s], value[s]);
		} else {
			int a, b;
            cin>>a>>b;
			int res = path(a, b);
            cout<<res<<" ";
		}
	}
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}