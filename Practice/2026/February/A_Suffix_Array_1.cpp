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

void solve()
{
    string str;
    cin >> str;
    str.push_back('$');
    const int n = sz(str);
    vector<int> p(n), c(n);
    vector<pair<int,int>> curr(n);
    for(int i = 0; i < n; i++)
        p[i] = i;
    sort(all(p), [&](int &a, int &b){
        return str[a] < str[b];
    });
    c[p[0]] = 0;
    for(int i = 1; i < n; i++){
        int &id = p[i], &prev = p[i - 1];
        if(str[id] == str[prev])
            c[id] = c[prev];
        else
            c[id] = c[prev] + 1;
    }
    for(int add = 1; add < n; add <<= 1){
        for(int i = 0; i < n; i++){
            curr[i] = {c[i], c[(i + add) % n]};
        }
        sort(all(p), [&](int &a, int &b){
            return curr[a] < curr[b];
        });
        for(int i = 1; i < n; i++){
            int &id = p[i], &prev = p[i - 1];
            if(curr[id] == curr[prev])
                c[id] = c[prev];
            else
                c[id] = c[prev] + 1;
        }
    }
    for(int i = 0; i < n; i++)
        cout << p[i] << (i == n - 1 ? '\n' : ' ');
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