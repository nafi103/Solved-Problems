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

// 1 -> unset true, 2 -> set false, 3 -> set true, 0 -> unset false

const int uf = 0, ut = 1, sf = 2, st = 3;

bool impossible(vector<int> &cnt){
    if(cnt[3] > 1 or cnt[1] > 1)
        return true;
    if(cnt[3] == 0 and cnt[1])
        return true;
    if(cnt[3] == 0 and cnt[2])
        return true;
    return false;
}

bool a_after_b(vector<vector<int>> &g,
    vector<int> &arr, vector<bool> &visited, int &n, int a, int b){
    fill(all(visited), false);
    vector<int> tcnt(4, 0);
    queue<int> q;
    for(int i = 0; i < n; i++){
        if(arr[i] == b){
            visited[i] = true;
            q.push(i);
        }
    }

    while(!q.empty()){
        int node = q.front();
        q.pop();
        tcnt[arr[node]]++;
        if(tcnt[a]){
            return true;
        }
        for(auto &adj: g[node]){
            if(!visited[adj]){
                visited[adj] = true;
                q.push(adj);
            }
        }
    }

    return false;
}

void a_push_b(vector<vector<int>> &g, vector<int> &arr, vector<bool> &visited, vector<int> &in_degree,
    vector<int> &order, int &n, int a, int b){
    queue<int> q;
    for(int i = 0; i < n; i++){
        if(arr[i] == a and in_degree[i] == 0 and !visited[i]){
            visited[i] = true;
            q.push(i);
        }
    }

    while(!q.empty()){
        int node = q.front();
        q.pop();
        order.push_back(node);
        for(auto &adj: g[node]){
            in_degree[adj]--;
            if(arr[adj] == b and in_degree[adj] == 0 and !visited[adj]){
                visited[adj] = true;
                q.push(adj);
            }
        }
    }
}

void solve()
{
    int n;
    string str;
    cin >> n;
    vector<vector<int>> g(n), r_g(n);
    vector<int> arr(n, 0), in_degree(n, 0), val_cnt(4, 0);
    vector<bool> visited(n);
    for(int i = 0; i < n; i++){
        cin >> str;
        if(str == "set")
            arr[i] |= 2;
        cin >> str;
        if(str == "true")
            arr[i] |= 1;
        val_cnt[arr[i]]++;
    }

    int m;
    cin >> m;
    while(m--){
        int u, v;
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        in_degree[v]++;
        r_g[v].push_back(u);
    }

    //Base case (no set true but unset false)
    if(impossible(val_cnt)){
        cout << -1 << endl;
        return;
    }

    if(val_cnt[2]){
        
        if(a_after_b(g, arr, visited, n, st, sf)){
            cout << -1 << endl;
            return;
        }

        if(a_after_b(r_g, arr, visited, n, ut, sf)){
            cout << -1 << endl;
            return;
        }
    }


    // if no unset true, no unset false should be after set true
    if(val_cnt[3] and val_cnt[1] == 0){
        if(a_after_b(g, arr, visited, n, uf, st)){
            cout << -1 << endl;
            return;
        }
    }

    // all unset false after set true, unset true should not be after those
    if(val_cnt[3] and val_cnt[1]){

        if(a_after_b(g, arr, visited, n, st, ut)){
            cout << -1 << endl;
            return;
        }

        vector<int> a;
        fill(all(visited), false);
        queue<int> q;
        for(int i = 0; i < n; i++){
            if(arr[i] == 3){
                visited[i] = true;
                q.push(i);
                break;
            }
        }

        while(!q.empty()){
            int node = q.front();
            q.pop();
            if(arr[node] == 0)
                a.push_back(node);
            for(auto &adj: g[node]){
                if(!visited[adj]){
                    visited[adj] = true;
                    q.push(adj);
                }
            }
        }

        fill(all(visited), false);
        for(auto &node: a){
            visited[node] = true;
            q.push(node);
        }

        while(!q.empty()){
            int node = q.front();
            q.pop();
            if(arr[node] == 1){
                cout << -1 << endl;
                return;
            }
            for(auto &adj: g[node]){
                if(!visited[adj]){
                    visited[adj] = true;
                    q.push(adj);
                }
            }
        }
    }

    fill(all(visited), false);
    vector<int> order;
    a_push_b(g, arr, visited, in_degree, order, n, uf, uf);
    a_push_b(g, arr, visited, in_degree, order, n, st, sf);
    a_push_b(g, arr, visited, in_degree, order, n, sf, sf);
    a_push_b(g, arr, visited, in_degree, order, n, ut, uf);
    a_push_b(g, arr, visited, in_degree, order, n, uf, uf);

    for(auto &x: order)
        cout << x + 1 << " ";
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}