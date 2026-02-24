#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 2e5 + 10;
int n, c[N], ans;
vector<vector<int>> t(N);
vector<map<int,int>> subtree_color(N);

void input(){
    ans = 0;
    cin >> n;
    for(int i = 0; i < n; i++){
        t[i].clear();
        subtree_color[i].clear();
        cin >> c[i];
    }
    int u, v;
    for(int i = 1; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
}

void dfs(int node, int par){
    int bc = -1, bcsz = -1;
    for(auto &child: t[node]){
        if(child ^ par){
            dfs(child, node);
            if(subtree_color[child].count(c[node])){
                int cnt = subtree_color[child][c[node]];
                ans += cnt;
                ans += (cnt * (cnt - 1)) / 2;
                subtree_color[child].erase(c[node]);
            }
            if(bcsz < sz(subtree_color[child])){
                bc = child;
                bcsz = sz(subtree_color[child]);
            }
        }
    }
    if(bc != -1){
        swap(subtree_color[bc], subtree_color[node]);
        for(auto &child: t[node]){
            if(child != par and child != bc){
                for(auto &[f, s]: subtree_color[child]){
                    subtree_color[node][f] += s;
                }
                subtree_color[child].clear();
            }
        }
    }
    subtree_color[node][c[node]] = 1;
}

void solve()
{
    input();
    dfs(0, -1);
    for(auto &[f, s]: subtree_color[0]){
        ans += (s * (s - 1)) / 2;
    }
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