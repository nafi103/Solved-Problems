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
    ll ans = 0;
    string str, str1;
    cin >> str >> str1;
    if (str.size() == str1.size())
    {
        bool flag = false;
        ll n = str.size();
        for (int i = 0; i < n; i++)
        {
            if (str[i] != str1[i] && flag == false)
            {
                flag = true;
                ans += abs(str[i] - str1[i]);
            }
            else if (flag)
            {
                ans += 9;
            }
        }
    }
    else
    {
        string mxstr = str.size() > str1.size() ? str : str1;
        ans += (mxstr[0]-'0');
        ans += ((mxstr.size() - 1) * 9);
    }
    cout << ans << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}