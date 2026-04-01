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
vector<vector<int>> id(3,vector<int>(N));
vector<pair<char,int>> parent(N);
int n;
const pair<char,int> dummy = {'$', -1};

void solve()
{
    cin >> n;
    for(int i = 0; i < 3; i++){
        for(int j = 1; j <= n; j++){
            cin >> id[i][j];
        }
    }
    fill(parent.begin(), parent.begin() + n + 1, dummy);
    int q = 1, k = 1, j = 1;
    for(int num = 2; num <= n; num++){
        bool possible = false;
        if(id[0][num] < id[0][q]){
            possible = true;
            parent[num] = {'q', q};
        }
        if(id[1][num] < id[1][k]){
            possible = true;
            parent[num] = {'k', k};
        }
        if(id[2][num] < id[2][j]){
            possible = true;
            parent[num] = {'j', j};
        }
        if(possible){
            if(id[0][q] < id[0][num])
                q = num;
            if(id[1][k] < id[1][num])
                k = num;
            if(id[2][j] < id[2][num])
                j = num;
        }
    }
    if(parent[n] == dummy){
        cout << "NO" << endl;
        return;
    }
    vector<pair<char,int>> path;
    int curr = n;
    while(curr > 1){
        auto [c, p] = parent[curr];
        path.push_back({c, curr});
        curr = p;
    }
    reverse(all(path));
    cout << "YES" << endl;
    cout << sz(path) << endl;
    for(auto &[c, x]: path)
        cout << c << " " << x << endl;
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