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
bool visited[N];
vector<vector<pair<int,int>>> g(N); // main graph
map<int,vector<pair<int,int>>> edge; // color -> {u, v} vector
 void input(){
    edge.clear();
    int n, m;
    cin >> n >> m;
    for(int i = 0; i < n; i++){
        visited[i] = false;
        g[i].clear();
    }
    for(int i = 0, u, v, c; i < m; i++){
        cin >> u >> v >> c;
        u--, v--;
        g[u].emplace_back(v, c);
        g[v].emplace_back(u, c);
        edge[c].push_back({u, v});
    }
}
 void solve()
{
    input();
    int b, e;
    cin >> b >> e;
    b--, e--;
    if(b == e){
        cout << 0 << endl;
        return;
    }
    set<int>curr, seen;
    visited[b] = true;
    for(auto &[nbr,c] : g[b]){
        curr.insert(c);
    }
    seen = curr;
    int d = 0;
    while(!visited[e]){
        d++;
        set<int> next;
        for(auto &c: curr){
            vector<pair<int,int>> &ref = edge[c];
            for(auto &[u, v]: ref){
                if(!visited[u]){
                    visited[u] = true;
                    for(auto &[nbr,col] : g[u]){
                        if(seen.count(col))
                            continue;
                        next.insert(col);
                        seen.insert(col);
                    }
                }
                if(!visited[v]){
                    visited[v] = true;
                    for(auto &[nbr,col] : g[v]){
                        if(seen.count(col))
                            continue;
                        next.insert(col);
                        seen.insert(col);
                    }
                }
            }
            edge.erase(c);
        }
        curr = next;
    }
    cout << d << endl;
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