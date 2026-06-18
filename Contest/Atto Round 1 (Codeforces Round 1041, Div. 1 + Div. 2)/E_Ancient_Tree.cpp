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
int n, k, c[N], saved[N];
long long w[N], ans;
vector<int> g[N];
set<int> sack[N];
 void input(){
    ans = 0;
    cin >> n >> k;
    for(int i = 0; i < n; i++){
        cin >> w[i];
        g[i].clear();
        sack[i].clear();
        saved[i] = 0;
    }
    for(int i = 0; i < n; i++){
        cin >> c[i];
    }
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        g[v].push_back(u);
    }
}
 void dfs1(int node, int parent){
    int big_child = -1, _size = -1;
     for(auto &child: g[node]){
        if(child != parent){
            dfs1(child, node);
             if(sz(sack[child]) > _size){
                _size = sz(sack[child]);
                big_child = child;
            }
        }
    }
     if(big_child != -1){
        swap(sack[big_child], sack[node]);
    }
     set<int> collisions;
    for(auto &child: g[node]){
        if(child != parent and child != big_child){
            for(auto &x: sack[child]){
                if(sack[node].count(x)){
                    collisions.insert(x);
                }
                sack[node].insert(x);
            }
            sack[child].clear();
        }
    }
     if(c[node]){
        sack[node].insert(c[node]);
        bool cutie = false;
        for(auto &x : collisions){
            if(x != c[node]){
                cutie = true;
                break;
            }
        }
        if(cutie) ans += w[node];
    }
    else{
        if(collisions.size() == 1){
            saved[node] = *collisions.begin();
        }
        else if(collisions.size() > 1){
            ans += w[node];
        }
    }
}
 void dfs2(int node, int parent, int p_color){
    if(c[node] == 0){
        if(saved[node]){
            c[node] = saved[node];
        }
        else{
            c[node] = p_color;
        }
    }
     for(auto &child: g[node]){
        if(child != parent){
            dfs2(child, node, c[node]);
        }
    }
}
 void solve()
{
    input();
    dfs1(0, -1);
    dfs2(0, -1, 1);
     cout << ans << "\n";
    for(int i = 0; i < n; i++)
        cout << c[i] << " \n"[i == n - 1];
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