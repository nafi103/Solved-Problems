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

struct DSU{
    vector<int>parent, _size;

    DSU(int n){
        parent.resize(n);
        iota(all(parent), 0);
        _size.assign(n, 1); 
    }
 
    int find(int i){ 
        if(parent[i] == i) return i; 
        return parent[i] = find(parent[i]); 
    }
    
    void Union(int a, int b){ 
        a = find(a); 
        b = find(b); 
        if(a == b) return; 
        if(_size[a] < _size[b]) swap(a,b);
        parent[b] = a; 
        _size[a] += _size[b]; 
    }
};

const int N = 2e5 + 5;
vector<pair<int,int>> edges(N);
int h[N];

void input(int &n, int &m){
    cin >> n >> m;
    for(int i = 1; i <= n; i++){
        cin >> h[i];
    }
    for(int i = 0; i < m; i++){
        cin >> edges[i].first >> edges[i].second;
    }
    sort(edges.begin(), edges.begin() + m, [&](pair<int,int> &a, pair<int,int>&b){
        return max(h[a.first],h[a.second]) < max(h[b.first], h[b.second]);
    });
}

void solve()
{
    int a, b, e, q, n, m;
    input(n, m);
    cin >> q;
    vector<array<int, 4>> query(q);
    vector<bool> ans(q, false);
    int p = 0;
    for(auto &[id, a, b, e]: query){
        cin >> a >> b >> e;
        id = p++;
    }
    sort(all(query), [&](array<int, 4> &a, array<int, 4> &b){
        return h[a[1]] + a[3] < h[b[1]] + b[3];
    });
    p = 0;
    DSU uf(n + 1);
    for(auto &[id, a, b, e]: query){
        int target = h[a] + e;
        while(p < m and max(h[edges[p].first], h[edges[p].second]) <= target){
            uf.Union(edges[p].first, edges[p].second);
            p++;
        }
        if(uf.find(a) == uf.find(b)){
            ans[id] = true;
        }
    }
    for(int i = 0; i < q; i++){
        if(ans[i])
            cout << "YES" << endl;
        else
            cout << "NO" << endl;
    }
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
        cout << endl;
    }
}