#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
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
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int n;
vector<vector<char>>grid;
map<pair<int,int>, int>ghost, human;

struct HopcroftKarp {
    int n, m;
    vector<vector<int>> g;
    vector<int> dist, pairU, pairV;
    static const int INF = 1e9;

    HopcroftKarp(int n_ = 0, int m_ = 0) {
        n = n_; m = m_;
        g.assign(n, {});
        pairU.assign(n, -1);
        pairV.assign(m, -1);
        dist.assign(n, 0);
    }

    void add_edge(int u, int v) {
        g[u].push_back(v);
    }

    bool bfs() {
        queue<int> q;
        for (int u = 0; u < n; ++u) {
            if (pairU[u] == -1) {
                dist[u] = 0;
                q.push(u);
            } else {
                dist[u] = INF;
            }
        }
        bool foundAug = false;
        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (int v : g[u]) {
                int u2 = pairV[v];
                if (u2 == -1) {
                    foundAug = true;
                } else if (dist[u2] == INF) {
                    dist[u2] = dist[u] + 1;
                    q.push(u2);
                }
            }
        }
        return foundAug;
    }

    bool dfs(int u) {
        for (int v : g[u]) {
            int u2 = pairV[v];
            if (u2 == -1 || (dist[u2] == dist[u] + 1 && dfs(u2))) {
                pairU[u] = v;
                pairV[v] = u;
                return true;
            }
        }
        dist[u] = INF;
        return false;
    }

    int max_matching() {
        int matching = 0;
        while (bfs()) {
            for (int u = 0; u < n; ++u)
                if (pairU[u] == -1 && dfs(u))
                    ++matching;
        }
        return matching;
    }

    vector<pair<int,int>> matching_edges() const {
        vector<pair<int,int>> res;
        for (int v = 0; v < m; ++v)
            if (pairV[v] != -1) res.emplace_back(pairV[v], v);
        return res;
    }
};

int dx[] = {1,-1,0,0};
int dy[] = {0,0,1,-1};

bool valid(int &i, int &j){
    return i>=0 and i<n and j>=0 and j<n and grid[i][j]!='#';
}

bool check(int len){
    queue<array<int,4>>q;
    for(auto &[f,s]: ghost){
        auto &[r,c] = f;
        q.push({r,c,0,s});
    }
    vector<vector<vector<bool>>>visited(sz(ghost),vector<vector<bool>>(n,vector<bool>(n,false)));
    HopcroftKarp hk(sz(ghost),sz(human));
    while(!q.empty()){
        auto [r,c,d,id] = q.front();
        q.pop();
        if(d>len or visited[id][r][c])
            continue;
        visited[id][r][c] = true;
        if(grid[r][c]=='H'){
            hk.add_edge(id,human[{r,c}]);
        }
        for(int i = 0; i<4; i++){
            int nr = r+dx[i], nc = c+dy[i];
            if(valid(nr,nc)){
                q.push({nr,nc,d+1,id});
            }
        }
    }
    return hk.max_matching()==sz(human);
}

int bs(int l, int r){
    if(l>r)
        return l;
    int mid = (l+r)/2;
    if(check(mid))
        return bs(l,mid-1);
    return bs(mid+1,r);
}


void solve()
{
    cin>>n;
    grid.clear();
    human.clear();
    ghost.clear();
    grid.resize(n,vector<char>(n));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            cin>>grid[i][j];
            if(grid[i][j]=='H'){
                human[{i,j}] = sz(human);
            }
            else if(grid[i][j]=='G'){
                ghost[{i,j}] = sz(ghost);
            }
        }
    }
    int ans = bs(0, n+n+40);
    if(ans<n+n+40){
        cout<<2*ans+2<<endl;
    }else{
        cout<<"Vuter Dol Kupokat"<<endl;
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}