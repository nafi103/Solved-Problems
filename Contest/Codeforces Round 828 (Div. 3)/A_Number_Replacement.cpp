#include<bits/stdc++.h>
using namespace std;
 void solution(){
    int n,flag = 1;
    string str;
    cin>>n;
    int arr[n];
    char arr2[n];
    for (int i = 0; i < n; i++)
    {
        cin>>arr[i];
    }
    cin>>str;
    for (int i = 0; i < n; i++)
    {
        char y = str[i];
        int x = arr[i];
        for (int j = 0; j < n; j++)
        {
            if (arr[j]== x)
            {
                arr2[j]= y;
            }
        }
    }
    for (int i = 0; i < n; i++)
    {
        if(arr2[i]!=str[i]){
            flag = 0;
            break;
        }
    }
    if(flag)    cout<<"YES"<<endl;
    else    cout<<"NO"<<endl;
    /* for (int i = 0; i < n; i++)
    {
        cout<<arr2[i];
    } */
}
 int main(){
    int t;
    cin>>t;
    while (t--) solution();
}