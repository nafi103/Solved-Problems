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

int travelTime(int n, int m, int l, int a[], int b[], int w[]) {

    vector<vector<pair<int,int>>> t(n);
    for(int i = 0; i < m; i++){
        int u = a[i], v = b[i], x = w[i];
        t[u].push_back({v, x});
        t[v].push_back({u, x});
    }

    vector<bool> visited(n, false);
    vector<int> d(n);

    auto get_distances = [&](auto& self, int node, int parent) -> void {
        d[node] = 0;
        visited[node] = true;

        for(auto &[child, w] : t[node]){
            if(child != parent){
                self(self, child, node);
                d[node] = max(d[node], d[child] + w);
            }
        }
    };

    auto get_suitable_node = [&](auto &self, int node) -> int {
        vector<int> pref = {0};
        for(auto &[child, w]: t[node]){
            pref.push_back(d[child] + w);
        }
        vector<int> suff = pref;
        suff.push_back(0);

        for(int i = 1; i < sz(pref); i++){
            pref[i] = max(pref[i], pref[i - 1]);
        }
        for(int i = sz(suff) - 2; i >= 0; i--){
            suff[i] = max(suff[i], suff[i + 1]);
        }

        for(int i = 0; i < sz(t[node]); i++){
            auto &[child, w] = t[node][i];
            int smx = max(pref[i], suff[i + 2]);
            int new_mx = max(smx + w, d[child]);

            if(new_mx < d[node]){
                d[node] = smx;
                d[child] = new_mx;
                return self(self, child);
            }
        }

        return node;
    };

    auto get_max_distance = [&](int node) -> int {
        int mx = 0, smx = 0;

        for(auto &[child, w]: t[node]){
            if(w + d[child] >= mx){
                smx = mx;
                mx = w + d[child];
            }else if(w + d[child] > smx){
                smx = w + d[child];
            }
        }

        return mx + smx;
    };

    int mx_sub = 0;
    vector<int> arr;
    for(int i = 0; i < n; i++){
        if(!visited[i]){
            get_distances(get_distances, i, -1);
            int node = get_suitable_node(get_suitable_node, i);
            mx_sub = max(mx_sub, get_max_distance(node));
            arr.push_back(d[node]);
        }
    }

    sort(rbegin(arr), rend(arr));

    if(sz(arr) >= 2){
        mx_sub = max(mx_sub, arr[0] + arr[1] + l);
    }

    if(sz(arr) >= 3){
        mx_sub = max(mx_sub, arr[1] + arr[2] + 2 * l);
    }

    return mx_sub;
}

void solve()
{
    int n, m, l;
    cin >> n >> m >> l;
    vector<int> a(m), b(m), w(m);
    for(auto &x: a)
        cin >> x;
    for(auto &y: b)
        cin >> y;
    for(auto &z: w)
        cin >> z;

    vector<vector<pair<int,int>>> t(n);
    for(int i = 0; i < m; i++){
        int u = a[i], v = b[i], x = w[i];
        t[u].push_back({v, x});
        t[v].push_back({u, x});
    }

    vector<bool> visited(n, false);
    vector<int> d(n);

    auto get_distances = [&](auto& self, int node, int parent) -> void {
        d[node] = 0;
        visited[node] = true;

        for(auto &[child, w] : t[node]){
            if(child != parent){
                self(self, child, node);
                d[node] = max(d[node], d[child] + w);
            }
        }
    };

    auto get_suitable_node = [&](auto &self, int node) -> int {
        vector<int> pref = {0};
        for(auto &[child, w]: t[node]){
            pref.push_back(d[child] + w);
        }
        vector<int> suff = pref;
        suff.push_back(0);

        for(int i = 1; i < sz(pref); i++){
            pref[i] = max(pref[i], pref[i - 1]);
        }
        for(int i = sz(suff) - 2; i >= 0; i--){
            suff[i] = max(suff[i], suff[i + 1]);
        }

        for(int i = 0; i < sz(t[node]); i++){
            auto &[child, w] = t[node][i];
            int smx = max(pref[i], suff[i + 2]);
            int new_mx = max(smx + w, d[child]);

            if(new_mx < d[node]){
                d[node] = smx;
                return self(self, child);
            }
        }

        return node;
    };

    auto get_max_distance = [&](int node) -> int {
        int mx = 0, smx = 0;

        for(auto &[child, w]: t[node]){
            if(w + d[child] >= mx){
                smx = mx;
                mx = w + d[child];
            }else if(w + d[child] > smx){
                smx = w + d[child];
            }
        }

        return mx + smx;
    };

    int mx_sub = 0;
    vector<int> arr;
    for(int i = 0; i < n; i++){
        if(!visited[i]){
            get_distances(get_distances, i, -1);
            int node = get_suitable_node(get_suitable_node, i);
            mx_sub = max(mx_sub, get_max_distance(node));
            arr.push_back(d[node]);
        }
    }

    sort(rbegin(arr), rend(arr));

    if(sz(arr) >= 2){
        mx_sub = max(mx_sub, arr[0] + arr[1] + l);
    }

    if(sz(arr) >= 3){
        mx_sub = max(mx_sub, arr[1] + arr[2] + 2 * l);
    }

    cout << mx_sub << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int z = 1;
    for (int zz = 1; zz <= z; zz++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}