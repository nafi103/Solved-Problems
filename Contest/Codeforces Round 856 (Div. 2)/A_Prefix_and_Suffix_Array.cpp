#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 void solve()
{
    bool flag = true;
    int n, i;
    string str1, str2, str = "";
    cin >> n;
    vector<string> v(2 * n - 2);
    readv(v);
    if (n == 2)
    {
        if (v[0] == v[1])
            yes;
        else
            no;
        return;
    }
    for (i = 0; i < 2 * n - 2; i++)
    {
        if (v[i].size() == n - 1)
        {
            str1 = v[i];
            break;
        }
    }
    for (++i; i < 2 * n - 2; i++)
    {
        if (v[i].size() == n - 1)
        {
            str2 = v[i];
            break;
        }
    }
    for (int i = 0; i < n - 1; i++)
    {
        if (str1[i] != str2[n - 2 - i])
        {
            flag = false;
            break;
        }
    }
    if (flag)
        yes;
    else
        no;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}