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
int arr[N], n, pref[N], prod[N];

void solve()
{
    cin >> n;
    vector<int> g_two;
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        if(arr[i] > 1)
            g_two.push_back(i);
        pref[i] = arr[i] + pref[i - 1];
        if(log(prod[i - 1]) + log(arr[i]) < log(inf))
            prod[i] = prod[i - 1] * arr[i];
        else
            prod[i] = inf;
    }
    if(prod[n] == inf){
        int l = 1, r = n;
        while(arr[l] == 1)
            l++;
        while(arr[r] == 1)
            r--;
        cout << l << " " << r << endl;
        return;
    }
    int m = sz(g_two), l = 1, r = 1, mx = 0;
    for(int i = 0; i < m - 1; i++){
        int p = g_two[i];
        for(int j = i + 1; j < m; j++){
            int q = g_two[j];
            int sum = pref[q] - pref[p - 1], mul = prod[q] / prod[p - 1];
            if(mul - sum > mx){
                mx = mul - sum;
                l = p;
                r = q;
            }
        }
    }
    cout << l << " " << r << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    prod[0] = 1;
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}