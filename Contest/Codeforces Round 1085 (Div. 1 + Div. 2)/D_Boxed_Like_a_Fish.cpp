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
 const int N = 5e5 + 10;
vector<vector<int>> t(N);
int mn[N], smn[N], jmn[N], jsmn[N], n, k, root;
bool junction[N];
 void input(){
    cin >> n >> k >> root;
    root--;
    for(int i = 0; i < n; i++){
        mn[i] = smn[i] = jmn[i] = jsmn[i] = inf;
        junction[i] = false;
        t[i].clear();
    }
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
}
 void dfs(int node, int par){
    if(sz(t[node]) == 1){
        mn[node] = 0;
        return;
    }
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node);
            if(mn[child] + 1 <= mn[node]){
                smn[node] = mn[node];
                mn[node] = mn[child] + 1;
            }else if(mn[child] + 1 < smn[node]){
                smn[node] = mn[child] + 1;
            }
        }
    }
}
 void reroot(int node, int par, int par_d){
    if(par_d < mn[node]){
        smn[node] = mn[node];
        mn[node] = par_d;
    }else if(par_d < smn[node])
        smn[node] = par_d;
     if((mn[node] + smn[node] <= k + 1) or sz(t[node]) == 1)
        junction[node] = true;
     for(auto &child: t[node]){
        if(child != par){
            if(mn[child] + 1 == mn[node])
                reroot(child, node, smn[node] + 1);
            else
                reroot(child, node, mn[node] + 1);
        }
    }
}
 void junction_distance(int node, int par){
    for(auto &child: t[node]){
        if(child != par){
            junction_distance(child, node);
            if(jmn[child] + 1 <= jmn[node]){
                jsmn[node] = jmn[node];
                jmn[node] = jmn[child] + 1;
            }else if(jmn[child] + 1 < jsmn[node]){
                jsmn[node] = jmn[child] + 1;
            }
        }
    }
    if(junction[node] or (jmn[node] + jsmn[node] <= k + 1)){
        jsmn[node] = jmn[node];
        jmn[node] = 0;
        junction[node] = true;
    }
}
 // To calculate for every node as root
// void junction_reroot(int node, int par, int par_d){
//     if(par_d < jmn[node]){
//         jsmn[node] = jmn[node];
//         jmn[node] = par_d;
//     }else if(par_d < jsmn[node])
//         jsmn[node] = par_d;
 //     for(auto &child: t[node]){
//         if(child != par){
//             if(jmn[child] + 1 == jmn[node])
//                 junction_reroot(child, node, jsmn[node] + 1);
//             else
//                 junction_reroot(child, node, jmn[node] + 1);
//         }
//     }
// }
 void solve()
{
    input();
    dfs(root, -1);
    reroot(root, -1, inf);
    if(junction[root]){
        cout << "YES" << endl;
        return;
    }
    junction_distance(root, -1);
    // junction_reroot(root, -1, inf);
    if(junction[root]){
        cout << "YES" << endl;
    }else{
        cout << "NO" << endl;
    }
    // for(int i = 0; i < n; i++){
    //     cerr << mn[i] << " \n"[i == n - 1];
    // }
    // for(int i = 0; i < n; i++){
    //     cerr << smn[i] << " \n"[i == n - 1];
    // }
    // for(int i = 0; i < n; i++){
    //     cerr << junction[i] << " \n"[i == n - 1];
    // }
    // cerr << endl;
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