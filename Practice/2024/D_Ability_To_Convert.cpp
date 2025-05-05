#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
const int inf = 1000000000000000010;
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)         \
    for (auto &x : v)     \
        cout << x << " "; \
    cout << endl
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)         \
    cerr << #x << " = "; \
    _print(x);           \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int expo(int a, int b)
{
    int res = 1;
    while (b > 0)
    {
        if(res<0) return inf;
        if (b & 1)
            res = (res * a);
        a = (a * a);
        b = b >> 1;
    }
    return (res<0? inf: res);
}

int dp[70][70];
int n;
string str;

int f(int pos, int power)
{
    if (pos == sz(str))
        return 0;
    if (dp[pos][power] != -1)
        return dp[pos][power];
    int &ans = dp[pos][power] = inf;
    string tmp = "";
    for (int i = pos; i < sz(str); i++)
    {
        tmp.pb(str[i]);
        reverse(all(tmp));
        if(sz(tmp)>18) break;
        int val = stoll(tmp);
        reverse(all(tmp));
        if(tmp.back()=='0' and (sz(tmp)>1)) continue;
        if (val < n)
        {
            int currAns = val * expo(n, power);
            currAns = (currAns<0? inf: currAns);
            currAns+= f(pos + sz(tmp), power + 1);
            currAns = (currAns<0? inf: currAns);
            ans = min(ans, currAns);
        }
        else
            break;
    }
    return ans;
}

void solve()
{
    int ans = inf;
    cin >> n >> str;
    reverse(all(str));
    memset(dp, -1, sizeof dp);
    cout << f(0, 0) << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // google(z);
        solve();
    }
}