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
    int n, k, i = 1;
    cin >> n;
    string str = "1";
    vector<int> v(n);
    readv(v);
    bool flag = true;
    k = *v.begin();
    for (i; i < n; i++)
    {
        if (v[i] >= k)
        {
            str.pb('1');
            k = v[i];
        }
        else if (v[i] < k && v[i] > v[0])
        {
            str.pb('0');
        }
        else
        {
            k = v[i];
            str.pb('1');
            i++;
            break;
        }
    }
    // cout << k <<" "<<v[0]<< endl;
    for (i; i < n; i++)
    {
        if (v[i] >= k && v[i] <= v[0])
        {
            str.pb('1');
            k = v[i];
        }
        else
        {
            str.pb('0');
        }
    }
    cout << str << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}