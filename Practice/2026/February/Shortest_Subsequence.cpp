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

map<char,int> base =
{
    {'A', 0},
    {'T', 1},
    {'C', 2},
    {'G', 3}
};

map<char,int> c = 

{
    {0, 'A'},
    {1, 'T'},
    {2, 'C'},
    {3, 'G'}
};

void solve()
{
    string str;
    cin >> str;
    int n = sz(str);
    vector<vector<int>> next(n, vector<int>(4, inf));
    for(int i = n - 2; i >= 0; i--){
        next[i] = next[i + 1];
        next[i][base[str[i + 1]]] = i + 1;
        if(i == 0)
            next[i][base[str[i]]] = i;
    }
    string ans = "";
    int i = 0;
    while(i < n){
        int mx = -1, id = -1;
        for(int j = 0; j < 4; j++){
            if(next[i][j] > mx){
                mx = next[i][j];
                id = j;
            }
        }
        ans.push_back(c[id]);
        i = mx;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}